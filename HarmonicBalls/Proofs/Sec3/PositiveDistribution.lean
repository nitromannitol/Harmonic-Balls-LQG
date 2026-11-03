import HarmonicBalls.Proofs.SecA.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Positive distributions are Radon measures

Used in Lemma A.5, Step 2 (eq:laplacian-of-v, lines 3797-3803): the distribution `σ = Δ v_t + t δ_z` is
nonnegative, hence a measure.

* `exists_measure_of_isPositiveOnTests`: a functional `S` on the test functions on an open `U ⊆ ℂ` which is
  linear and nonnegative on nonnegative test functions is integration against a measure `σ` with `σ(Uᶜ) = 0`
  and `σ(K) < ∞` for compact `K ⊆ U`. Route: `|S φ - S ψ| ≤ M S(χ)` for test functions supported in a compact
  `K` with `|φ - ψ| ≤ M` and a cut-off `χ = 1` on `K` (positivity); `S` extends to the continuous functions with
  compact support in `U` by mollification (`mollifiedExtension`, uniform convergence of `ρ_n ⋆ f`); the
  extension is a positive linear functional on `C_c(U, ℝ)`, represented by the Riesz–Markov–Kakutani measure
  (Mathlib `RealRMK.rieszMeasure`), pushed forward to `ℂ`.
* `measure_le_of_integral_le`: on an open `V`, test-function integrals control the measure of `V`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian
open scoped ContDiff CompactlySupported ENNReal

/-! ## Test functions -/

theorem tsupport_const_mul_add_const_mul_subset (f g : ℂ → ℝ) (a b : ℝ) :
    tsupport (fun x => a * f x + b * g x) ⊆ tsupport f ∪ tsupport g := by
  refine closure_minimal (fun x hx => ?_) ((isClosed_tsupport f).union (isClosed_tsupport g))
  by_contra h
  rw [mem_union, not_or] at h
  exact hx (by simp [image_eq_zero_of_notMem_tsupport h.1, image_eq_zero_of_notMem_tsupport h.2])

/-- Linearity of the pairing `⟨w, Δφ⟩` on test functions. -/
theorem integral_mul_laplacian_const_mul_add_const_mul {U : Set ℂ} {w : ℂ → ℝ} (hw : LocallyIntegrableOn w U)
    {φ ψ : ℂ → ℝ} (hφ : IsTestFunction U φ) (hψ : IsTestFunction U ψ) (a b : ℝ) :
    ∫ x, w x * Δ (fun y => a * φ y + b * ψ y) x = a * (∫ x, w x * Δ φ x) + b * ∫ x, w x * Δ ψ x := by
  have e : (fun x => w x * Δ (fun y => a * φ y + b * ψ y) x) =
      fun x => a * (w x * Δ φ x) + b * (w x * Δ ψ x) := by
    funext x
    have h2 : ∀ f : ℂ → ℝ, ContDiff ℝ ∞ f → ContDiffAt ℝ 2 f x := fun f hf =>
      (hf.of_le (by norm_num)).contDiffAt
    have haφ : Δ (fun y => a * φ y) x = a * Δ φ x :=
      InnerProductSpace.laplacian_smul (𝕜 := ℝ) (f := φ) (x := x) a (h2 φ hφ.1)
    have hbψ : Δ (fun y => b * ψ y) x = b * Δ ψ x :=
      InnerProductSpace.laplacian_smul (𝕜 := ℝ) (f := ψ) (x := x) b (h2 ψ hψ.1)
    have hadd : Δ (fun y => a * φ y + b * ψ y) x = Δ (fun y => a * φ y) x + Δ (fun y => b * ψ y) x :=
      ContDiffAt.laplacian_add (f₁ := fun y => a * φ y) (f₂ := fun y => b * ψ y)
        ((h2 φ hφ.1).const_smul a) ((h2 ψ hψ.1).const_smul b)
    rw [hadd, haφ, hbψ]; ring
  rw [e, integral_add ((integrable_mul_laplacian hw hφ).const_mul a)
    ((integrable_mul_laplacian hw hψ).const_mul b), integral_const_mul, integral_const_mul]

/-! ## Positive functionals on test functions -/

/-- `S` is linear on the test functions on `U`. -/
def IsLinearOnTests (U : Set ℂ) (S : (ℂ → ℝ) → ℝ) : Prop :=
  ∀ φ ψ, IsTestFunction U φ → IsTestFunction U ψ → ∀ a b : ℝ,
    S (fun x => a * φ x + b * ψ x) = a * S φ + b * S ψ

/-- `S` is nonnegative on the nonnegative test functions on `U` (a positive distribution). -/
def IsPositiveOnTests (U : Set ℂ) (S : (ℂ → ℝ) → ℝ) : Prop :=
  ∀ φ, IsTestFunction U φ → (∀ x, 0 ≤ φ x) → 0 ≤ S φ

section Positive

variable {U : Set ℂ} {S : (ℂ → ℝ) → ℝ}

/-- **Positivity gives continuity in the sup norm**: for test functions `φ, ψ` with `|φ - ψ| ≤ M` and a
nonnegative test function `χ = 1` on their supports, `|S φ - S ψ| ≤ M S(χ)`. -/
theorem abs_sub_le_mul_of_isPositiveOnTests (hlin : IsLinearOnTests U S) (hpos : IsPositiveOnTests U S)
    {χ φ ψ : ℂ → ℝ} (hχ : IsTestFunction U χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hφ : IsTestFunction U φ) (hψ : IsTestFunction U ψ)
    (hχ1 : ∀ x ∈ tsupport φ ∪ tsupport ψ, χ x = 1) {M : ℝ} (hM : ∀ x, |φ x - ψ x| ≤ M) :
    |S φ - S ψ| ≤ M * S χ := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set d : ℂ → ℝ := fun x => 1 * φ x + (-1) * ψ x with hd
  have hdx : ∀ x, d x = φ x - ψ x := fun x => by simp only [hd]; ring
  have hdT : IsTestFunction U d := hφ.const_mul_add_const_mul hψ 1 (-1)
  have hSd : S d = S φ - S ψ := by rw [hd, hlin φ ψ hφ hψ]; ring
  have hp : ∀ s : ℝ, |s| ≤ 1 → 0 ≤ S (fun x => M * χ x + s * d x) := by
    intro s hs
    refine hpos _ (hχ.const_mul_add_const_mul hdT M s) fun x => ?_
    by_cases hx : x ∈ tsupport φ ∪ tsupport ψ
    · rw [hχ1 x hx]
      have h1 : |d x| ≤ M := by rw [hdx]; exact hM x
      have h2 : |s * d x| ≤ M := by
        rw [abs_mul]; nlinarith [abs_nonneg s, abs_nonneg (d x)]
      linarith [neg_abs_le (s * d x)]
    · have : d x = 0 := image_eq_zero_of_notMem_tsupport fun h =>
        hx (tsupport_const_mul_add_const_mul_subset φ ψ 1 (-1) h)
      rw [this, mul_zero, add_zero]
      exact mul_nonneg hM0 (hχ0 x)
  have h1 := hp 1 (by simp)
  have h2 := hp (-1) (by simp)
  rw [hlin χ d hχ hdT] at h1 h2
  rw [abs_le, ← hSd]
  constructor <;> linarith

/-! ## Mollification -/

/-- The bump function of outer radius `1/(n+1)` centred at `0`. -/
noncomputable def mollifierBump (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : (0 : ℝ) < n + 1 := by positivity
    exact one_div_lt_one_div_of_lt this (by linarith)

/-- Mollification of `f` at scale `1/(n+1)`: `ρ_n ⋆ f` with the normalized bump `ρ_n` of `mollifierBump n`. -/
noncomputable def mollify (n : ℕ) (f : ℂ → ℝ) : ℂ → ℝ :=
  convolution ((mollifierBump n).normed volume) f (ContinuousLinearMap.lsmul ℝ ℝ) volume

theorem mollify_nonneg (n : ℕ) {f : ℂ → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ℂ) : 0 ≤ mollify n f x := by
  rw [mollify, convolution_def]
  exact integral_nonneg fun t => by
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    exact mul_nonneg ((mollifierBump n).nonneg_normed t) (hf _)

theorem mollify_const_mul_add_const_mul (n : ℕ) {f g : ℂ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (a b : ℝ) : mollify n (fun x => a * f x + b * g x) = fun x => a * mollify n f x + b * mollify n g x := by
  have hρc : HasCompactSupport ((mollifierBump n).normed (volume : Measure ℂ)) :=
    (mollifierBump n).hasCompactSupport_normed
  have hρ : Continuous ((mollifierBump n).normed (volume : Measure ℂ)) := (mollifierBump n).continuous_normed
  have hex : ∀ h : ℂ → ℝ, Continuous h →
      ConvolutionExists ((mollifierBump n).normed volume) h (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    fun h hh => hρc.convolutionExists_left _ hρ hh.locallyIntegrable
  have e : (fun x => a * f x + b * g x) = a • f + b • g := by funext x; simp [smul_eq_mul]
  rw [mollify, e, (hex (a • f) (hf.const_smul a)).distrib_add (hex (b • g) (hg.const_smul b)),
    convolution_smul, convolution_smul]
  funext x
  simp [mollify, smul_eq_mul]

theorem exists_abs_mollify_sub_le {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {ε : ℝ}
    (hε : 0 < ε) : ∃ N : ℕ, ∀ n ≥ N, ∀ x, |mollify n f x - f x| ≤ ε := by
  obtain ⟨r, hr, hfr⟩ := Metric.uniformContinuous_iff.1 (hfc.uniformContinuous_of_continuous hf) ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hr
  refine ⟨N, fun n hn x => ?_⟩
  have hρ : (mollifierBump n).rOut < r := by
    refine lt_of_le_of_lt ?_ hN
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have := (mollifierBump n).dist_normed_convolution_le (μ := (volume : Measure ℂ)) (x₀ := x)
    hf.aestronglyMeasurable fun y hy => (hfr (lt_trans (mem_ball.1 hy) hρ)).le
  rwa [Real.dist_eq] at this

theorem isTestFunction_mollify {U : Set ℂ} {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {δ : ℝ} (hδU : cthickening δ (tsupport f) ⊆ U) {n : ℕ} (hn : 1 / ((n : ℝ) + 1) ≤ δ) :
    IsTestFunction U (mollify n f) ∧ tsupport (mollify n f) ⊆ cthickening δ (tsupport f) := by
  have hρc : HasCompactSupport ((mollifierBump n).normed (volume : Measure ℂ)) :=
    (mollifierBump n).hasCompactSupport_normed
  have hsupp : Function.support (mollify n f) ⊆ cthickening δ (tsupport f) := by
    intro x hx
    unfold mollify at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 (support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hx)
    rw [ContDiffBump.support_normed_eq] at ha
    refine mem_cthickening_of_dist_le _ b _ _ (subset_tsupport f hb) ?_
    rw [dist_eq_norm, add_sub_cancel_right]
    exact (mem_ball_zero_iff.1 ha).le.trans hn
  have hts : tsupport (mollify n f) ⊆ cthickening δ (tsupport f) := closure_minimal hsupp isClosed_cthickening
  refine ⟨⟨?_, ?_, hts.trans hδU⟩, hts⟩
  · exact HasCompactSupport.contDiff_convolution_left (n := ⊤) (ContinuousLinearMap.lsmul ℝ ℝ) hρc
      (mollifierBump n).contDiff_normed hf.locallyIntegrable
  · exact hfc.isCompact.cthickening.of_isClosed_subset (isClosed_tsupport _) hts

theorem exists_mollify_isTestFunction (hU : IsOpen U) {f : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ U ∧ tsupport f ⊆ K ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
      IsTestFunction U (mollify n f) ∧ tsupport (mollify n f) ⊆ K := by
  obtain ⟨δ, hδ, hδU⟩ := hfc.isCompact.exists_cthickening_subset_open hU hfU
  obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hδ
  refine ⟨cthickening δ (tsupport f), hfc.isCompact.cthickening, hδU, self_subset_cthickening _, N₀,
    fun n hn => isTestFunction_mollify hf hfc hδU ?_⟩
  refine le_trans ?_ hN₀.le
  have : (N₀ : ℝ) ≤ n := by exact_mod_cast hn
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-! ## The extension of a positive distribution to `C_c` -/

/-- The extension of `S` to continuous functions with compact support, `f ↦ lim_n S(ρ_n ⋆ f)`. -/
noncomputable def mollifiedExtension (S : (ℂ → ℝ) → ℝ) (f : ℂ → ℝ) : ℝ :=
  limUnder atTop fun n => S (mollify n f)

theorem tendsto_mollifiedExtension (hU : IsOpen U) (hlin : IsLinearOnTests U S) (hpos : IsPositiveOnTests U S)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    Tendsto (fun n => S (mollify n f)) atTop (𝓝 (mollifiedExtension S f)) := by
  obtain ⟨K, hK, hKU, -, N₀, hN₀⟩ := exists_mollify_isTestFunction hU hf hfc hfU
  obtain ⟨χ, hχd, hχc, hχU, hχ01, hχ1⟩ := exists_cutoff_of_isCompact_subset_isOpen hK hU hKU
  have hχ : IsTestFunction U χ := ⟨hχd, hχc, hχU⟩
  have hSχ : 0 ≤ S χ := hpos χ hχ fun x => (hχ01 x).1
  refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
  rw [Metric.cauchySeq_iff']
  intro ε hε
  set ε' := ε / (2 * (S χ + 1)) with hε'def
  have hε' : 0 < ε' := div_pos hε (by linarith)
  have hε'e : 2 * ε' * (S χ + 1) = ε := by
    rw [hε'def]; field_simp
  obtain ⟨N, hN⟩ := exists_abs_mollify_sub_le hf hfc hε'
  refine ⟨max N N₀, fun n hn => ?_⟩
  have hn' : N ≤ n ∧ N₀ ≤ n := ⟨(le_max_left _ _).trans hn, (le_max_right _ _).trans hn⟩
  obtain ⟨hTn, hKn⟩ := hN₀ n hn'.2
  obtain ⟨hTm, hKm⟩ := hN₀ (max N N₀) (le_max_right _ _)
  have hb := abs_sub_le_mul_of_isPositiveOnTests hlin hpos hχ (fun x => (hχ01 x).1) hTn hTm
    (fun x hx => hχ1 x (hx.elim (fun h => hKn h) fun h => hKm h)) (M := 2 * ε') fun x => by
      have h1 := hN n hn'.1 x
      have h2 := hN (max N N₀) (le_max_left _ _) x
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith
  rw [Real.dist_eq]
  calc |S (mollify n f) - S (mollify (max N N₀) f)| ≤ 2 * ε' * S χ := hb
    _ < ε := by nlinarith

theorem mollifiedExtension_eq (hU : IsOpen U) (hlin : IsLinearOnTests U S) (hpos : IsPositiveOnTests U S)
    {φ : ℂ → ℝ} (hφ : IsTestFunction U φ) : mollifiedExtension S φ = S φ := by
  have hc : Continuous φ := hφ.1.continuous
  refine tendsto_nhds_unique (tendsto_mollifiedExtension hU hlin hpos hc hφ.2.1 hφ.2.2) ?_
  obtain ⟨K, hK, hKU, hφK, N₀, hN₀⟩ := exists_mollify_isTestFunction hU hc hφ.2.1 hφ.2.2
  obtain ⟨χ, hχd, hχc, hχU, hχ01, hχ1⟩ := exists_cutoff_of_isCompact_subset_isOpen hK hU hKU
  have hχ : IsTestFunction U χ := ⟨hχd, hχc, hχU⟩
  have hSχ : 0 ≤ S χ := hpos χ hχ fun x => (hχ01 x).1
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := ε / (2 * (S χ + 1)) with hε'def
  have hε' : 0 < ε' := div_pos hε (by linarith)
  have hε'e : 2 * ε' * (S χ + 1) = ε := by
    rw [hε'def]; field_simp
  obtain ⟨N, hN⟩ := exists_abs_mollify_sub_le hc hφ.2.1 hε'
  refine ⟨max N N₀, fun n hn => ?_⟩
  obtain ⟨hTn, hKn⟩ := hN₀ n ((le_max_right _ _).trans hn)
  have hb := abs_sub_le_mul_of_isPositiveOnTests hlin hpos hχ (fun x => (hχ01 x).1) hTn hφ
    (fun x hx => hχ1 x (hx.elim (fun h => hKn h) fun h => hφK h)) (hN n ((le_max_left _ _).trans hn))
  rw [Real.dist_eq]
  calc |S (mollify n φ) - S φ| ≤ ε' * S χ := hb
    _ < ε := by nlinarith

theorem mollifiedExtension_const_mul_add_const_mul (hU : IsOpen U) (hlin : IsLinearOnTests U S)
    (hpos : IsPositiveOnTests U S) {f g : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ U) (hg : Continuous g) (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ U) (a b : ℝ) :
    mollifiedExtension S (fun x => a * f x + b * g x) =
      a * mollifiedExtension S f + b * mollifiedExtension S g := by
  have hfg : Continuous fun x => a * f x + b * g x := (continuous_const.mul hf).add (continuous_const.mul hg)
  have hts := tsupport_const_mul_add_const_mul_subset f g a b
  have hfgc : HasCompactSupport fun x => a * f x + b * g x :=
    (hfc.isCompact.union hgc.isCompact).of_isClosed_subset (isClosed_tsupport _) hts
  refine tendsto_nhds_unique
    (tendsto_mollifiedExtension hU hlin hpos hfg hfgc (hts.trans (union_subset hfU hgU))) ?_
  obtain ⟨_, _, _, _, N₁, hN₁⟩ := exists_mollify_isTestFunction hU hf hfc hfU
  obtain ⟨_, _, _, _, N₂, hN₂⟩ := exists_mollify_isTestFunction hU hg hgc hgU
  refine (((tendsto_mollifiedExtension hU hlin hpos hf hfc hfU).const_mul a).add
    ((tendsto_mollifiedExtension hU hlin hpos hg hgc hgU).const_mul b)).congr' ?_
  filter_upwards [eventually_ge_atTop (max N₁ N₂)] with n hn
  rw [mollify_const_mul_add_const_mul n hf hg a b,
    hlin _ _ (hN₁ n ((le_max_left _ _).trans hn)).1 (hN₂ n ((le_max_right _ _).trans hn)).1]

theorem mollifiedExtension_nonneg (hU : IsOpen U) (hlin : IsLinearOnTests U S) (hpos : IsPositiveOnTests U S)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) (hf0 : ∀ x, 0 ≤ f x) :
    0 ≤ mollifiedExtension S f := by
  obtain ⟨_, _, _, _, N₀, hN₀⟩ := exists_mollify_isTestFunction hU hf hfc hfU
  refine ge_of_tendsto (tendsto_mollifiedExtension hU hlin hpos hf hfc hfU) ?_
  filter_upwards [eventually_ge_atTop N₀] with n hn
  exact hpos _ (hN₀ n hn).1 (mollify_nonneg n hf0)

end Positive

/-! ## Extension by zero from an open set -/

open Classical in
/-- Extension by zero of a compactly supported continuous function on `U`. -/
noncomputable def extendByZero {U : Set ℂ} (F : C_c(U, ℝ)) : ℂ → ℝ :=
  fun x => if h : x ∈ U then F ⟨x, h⟩ else 0

theorem extendByZero_of_mem {U : Set ℂ} (F : C_c(U, ℝ)) {x : ℂ} (h : x ∈ U) :
    extendByZero F x = F ⟨x, h⟩ := by
  simp [extendByZero, h]

theorem extendByZero_of_notMem {U : Set ℂ} (F : C_c(U, ℝ)) {x : ℂ} (h : x ∉ U) : extendByZero F x = 0 := by
  simp [extendByZero, h]

theorem tsupport_extendByZero_subset {U : Set ℂ} (F : C_c(U, ℝ)) :
    tsupport (extendByZero F) ⊆ Subtype.val '' tsupport F := by
  have hKc : IsCompact (Subtype.val '' tsupport F) :=
    F.hasCompactSupport.isCompact.image continuous_subtype_val
  refine closure_minimal (fun x hx => ?_) hKc.isClosed
  by_cases h : x ∈ U
  · rw [Function.mem_support, extendByZero_of_mem F h] at hx
    exact ⟨⟨x, h⟩, subset_tsupport _ hx, rfl⟩
  · exact absurd (extendByZero_of_notMem F h) hx

theorem tsupport_extendByZero_subset_open {U : Set ℂ} (F : C_c(U, ℝ)) : tsupport (extendByZero F) ⊆ U :=
  (tsupport_extendByZero_subset F).trans (by rintro _ ⟨y, -, rfl⟩; exact y.2)

theorem hasCompactSupport_extendByZero {U : Set ℂ} (F : C_c(U, ℝ)) : HasCompactSupport (extendByZero F) :=
  (F.hasCompactSupport.isCompact.image continuous_subtype_val).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_extendByZero_subset F)

theorem continuous_extendByZero {U : Set ℂ} (hU : IsOpen U) (F : C_c(U, ℝ)) : Continuous (extendByZero F) := by
  refine ContinuousOn.continuous_of_tsupport_subset ?_ hU (tsupport_extendByZero_subset_open F)
  rw [continuousOn_iff_continuous_domRestrict]
  have : U.domRestrict (extendByZero F) = F := by
    funext x
    rw [Set.domRestrict_apply, extendByZero_of_mem F x.2]
  rw [this]
  exact F.continuous

theorem extendByZero_add {U : Set ℂ} (F G : C_c(U, ℝ)) :
    extendByZero (F + G) = fun x => 1 * extendByZero F x + 1 * extendByZero G x := by
  funext x
  by_cases h : x ∈ U <;> simp [extendByZero, h]

theorem extendByZero_smul {U : Set ℂ} (c : ℝ) (F : C_c(U, ℝ)) :
    extendByZero (c • F) = fun x => c * extendByZero F x + 0 * extendByZero F x := by
  funext x
  by_cases h : x ∈ U <;> simp [extendByZero, h]

/-! ## Positive distributions are measures -/

/-- **A positive distribution is a measure** (Riesz–Markov–Kakutani). If `S` is linear on the test functions on
the open set `U` and `S φ ≥ 0` for nonnegative test functions `φ`, then there is a measure `σ` carried by `U`
(`σ(Uᶜ) = 0`), finite on compact subsets of `U`, with `∫ φ dσ = S φ` for every test function `φ` on `U`. -/
theorem exists_measure_of_isPositiveOnTests {U : Set ℂ} {S : (ℂ → ℝ) → ℝ} (hU : IsOpen U)
    (hlin : IsLinearOnTests U S) (hpos : IsPositiveOnTests U S) :
    ∃ σ : Measure ℂ, σ Uᶜ = 0 ∧ (∀ K, IsCompact K → K ⊆ U → σ K < ⊤) ∧
      ∀ φ, IsTestFunction U φ → Integrable φ σ ∧ ∫ x, φ x ∂σ = S φ := by
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  have hadm : ∀ F : C_c(U, ℝ), Continuous (extendByZero F) ∧ HasCompactSupport (extendByZero F) ∧
      tsupport (extendByZero F) ⊆ U := fun F =>
    ⟨continuous_extendByZero hU F, hasCompactSupport_extendByZero F, tsupport_extendByZero_subset_open F⟩
  let Λ₀ : C_c(U, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun F => mollifiedExtension S (extendByZero F)
      map_add' := fun F G => by
        rw [extendByZero_add, mollifiedExtension_const_mul_add_const_mul hU hlin hpos (hadm F).1 (hadm F).2.1
          (hadm F).2.2 (hadm G).1 (hadm G).2.1 (hadm G).2.2]
        ring
      map_smul' := fun c F => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [extendByZero_smul, mollifiedExtension_const_mul_add_const_mul hU hlin hpos (hadm F).1
          (hadm F).2.1 (hadm F).2.2 (hadm F).1 (hadm F).2.1 (hadm F).2.2]
        ring }
  let Λ : C_c(U, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ Λ₀ fun F hF =>
    mollifiedExtension_nonneg hU hlin hpos (hadm F).1 (hadm F).2.1 (hadm F).2.2 fun x => by
      by_cases h : x ∈ U
      · rw [extendByZero_of_mem F h]
        exact hF ⟨x, h⟩
      · rw [extendByZero_of_notMem F h]
  refine ⟨(RealRMK.rieszMeasure Λ).map Subtype.val, ?_, ?_, ?_⟩
  · rw [Measure.map_apply measurable_subtype_coe hU.isClosed_compl.measurableSet]
    have : (Subtype.val ⁻¹' Uᶜ : Set U) = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx => hx x.2
    rw [this, measure_empty]
  · intro K hK hKU
    rw [Measure.map_apply measurable_subtype_coe hK.isClosed.measurableSet]
    apply IsCompact.measure_lt_top
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hKU]
    exact hK
  · intro φ hφ
    have hc : Continuous φ := hφ.1.continuous
    have hcs : HasCompactSupport (fun x : U => φ x) := by
      have hpre : IsCompact (Subtype.val ⁻¹' tsupport φ : Set U) := by
        rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hφ.2.2]
        exact hφ.2.1
      exact hpre.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_comp_subset_preimage φ continuous_subtype_val)
    let Φ : C_c(U, ℝ) := ⟨⟨fun x => φ x, hc.comp continuous_subtype_val⟩, hcs⟩
    have hext : extendByZero Φ = φ := by
      funext x
      by_cases h : x ∈ U
      · rw [extendByZero_of_mem Φ h]
        rfl
      · rw [extendByZero_of_notMem Φ h]
        exact (image_eq_zero_of_notMem_tsupport fun hx => h (hφ.2.2 hx)).symm
    have hint : Integrable (fun x : U => φ x) (RealRMK.rieszMeasure Λ) :=
      Φ.continuous.integrable_of_hasCompactSupport Φ.hasCompactSupport
    refine ⟨(integrable_map_measure hc.aestronglyMeasurable measurable_subtype_coe.aemeasurable).2 hint, ?_⟩
    rw [integral_map measurable_subtype_coe.aemeasurable hc.aestronglyMeasurable]
    have h1 := RealRMK.integral_rieszMeasure Λ Φ
    change ∫ x, Φ x ∂(RealRMK.rieszMeasure Λ) = S φ
    rw [h1]
    change mollifiedExtension S (extendByZero Φ) = S φ
    rw [hext]
    exact mollifiedExtension_eq hU hlin hpos hφ

/-! ## Comparison of measures on open sets -/

/-- An open set of the plane is exhausted by compact sets: a bound on the measures of its compact subsets bounds
its measure. -/
theorem measure_isOpen_le_of_forall_isCompact {V : Set ℂ} (hV : IsOpen V) (ν : Measure ℂ) {c : ℝ≥0∞}
    (h : ∀ K, IsCompact K → K ⊆ V → ν K ≤ c) : ν V ≤ c := by
  obtain ⟨F, hFc, hFV, hFU, hFm⟩ := hV.exists_iUnion_isClosed
  set K : ℕ → Set ℂ := fun n => F n ∩ closedBall 0 n with hKdef
  have hKm : Monotone K := fun m n hmn =>
    inter_subset_inter (hFm hmn) (closedBall_subset_closedBall (by exact_mod_cast hmn))
  have hKU : ⋃ n, K n = V := by
    apply Subset.antisymm (iUnion_subset fun n => inter_subset_left.trans (hFV n))
    intro x hx
    rw [← hFU] at hx
    obtain ⟨m, hm⟩ := mem_iUnion.1 hx
    obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
    refine mem_iUnion.2 ⟨max m k, hFm (le_max_left _ _) hm, mem_closedBall_zero_iff.2 (hk.trans ?_)⟩
    exact_mod_cast le_max_right m k
  rw [← hKU, hKm.measure_iUnion]
  exact iSup_le fun n => h _ ((isCompact_closedBall 0 n).inter_left (hFc n)) (inter_subset_left.trans (hFV n))

/-- **Comparison on open sets.** If `∫ φ dν₁ ≤ ∫ φ dν₂` for all test functions `0 ≤ φ ≤ 1` on the open set `V`
(both integrable), then `ν₁(V) ≤ ν₂(V)`. -/
theorem measure_le_of_integral_le {V : Set ℂ} (hV : IsOpen V) {ν₁ ν₂ : Measure ℂ}
    (h : ∀ φ, IsTestFunction V φ → (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) →
      Integrable φ ν₁ ∧ Integrable φ ν₂ ∧ ∫ x, φ x ∂ν₁ ≤ ∫ x, φ x ∂ν₂) :
    ν₁ V ≤ ν₂ V := by
  apply measure_isOpen_le_of_forall_isCompact hV
  intro K hK hKV
  obtain ⟨χ, hχd, hχc, hχU, hχ01, hχ1⟩ := exists_cutoff_of_isCompact_subset_isOpen hK hV hKV
  obtain ⟨hi₁, hi₂, hle⟩ := h χ ⟨hχd, hχc, hχU⟩ hχ01
  have hnn : ∀ ν : Measure ℂ, 0 ≤ᵐ[ν] χ := fun ν => Eventually.of_forall fun x => (hχ01 x).1
  calc ν₁ K = ∫⁻ x, K.indicator 1 x ∂ν₁ := (lintegral_indicator_one hK.measurableSet).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal (χ x) ∂ν₁ := lintegral_mono fun x => by
        by_cases hx : x ∈ K
        · simp [hx, hχ1 x hx]
        · simp [hx]
    _ = ENNReal.ofReal (∫ x, χ x ∂ν₁) := (ofReal_integral_eq_lintegral_ofReal hi₁ (hnn ν₁)).symm
    _ ≤ ENNReal.ofReal (∫ x, χ x ∂ν₂) := ENNReal.ofReal_le_ofReal hle
    _ = ∫⁻ x, ENNReal.ofReal (χ x) ∂ν₂ := ofReal_integral_eq_lintegral_ofReal hi₂ (hnn ν₂)
    _ ≤ ∫⁻ x, V.indicator 1 x ∂ν₂ := lintegral_mono fun x => by
        by_cases hx : x ∈ V
        · simp only [indicator_of_mem hx, Pi.one_apply]
          exact ENNReal.ofReal_le_one.2 (hχ01 x).2
        · have : χ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hχU h)
          simp [hx, this]
    _ = ν₂ V := lintegral_indicator_one hV.measurableSet

end HarmonicBalls
