import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.Harmonic.MeanValue

/-!
# The minimum principle on discs and the Poisson integral of a disc

Generic potential theory in the plane used by Appendix A (sec:obstacle-appendix) of the corrected draft of
Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795), in the proof of
Lemma A.1 (lemma:appendix-basic-properties, line 3589). Classical references: Armitage and Gardiner, *Classical
potential theory* (AG01), Chapters 1 and 3.

Superharmonicity is expressed here through explicit predicates (lower semicontinuity and the super-mean-value
inequality on circles), so that this file depends on Mathlib only.

## Main results

* `nonneg_of_lowerSemicontinuousOn_of_superMean`: the **minimum principle** on a disc `B_R(c)` for a lower
  semicontinuous function with the local super-mean-value property whose lower limits at `∂B_R(c)` are `≥ 0`
  (AG01 Thm 3.2.2 / Cor 3.2.3 for discs).
* `discPoissonIntegral`, `harmonicOnNhd_discPoissonIntegral`, `tendsto_discPoissonIntegral_of_continuousOn`: the
  Poisson integral of a disc is harmonic and solves the Dirichlet problem for continuous boundary data.
* `exists_continuous_tendsto_of_lowerSemicontinuousOn`: inf-convolution approximation from below (Baire).
* `circleAverage_le_of_localSuperMean`: the local super-mean-value property is global (AG01 Thm 3.2.2).
* `discPoissonIntegral_le` (Poisson inequality) and `eventually_lt_discPoissonIntegral` (lower boundary limits).
-/

namespace HarmonicBalls

open Complex Metric Real Filter Topology Set MeasureTheory InnerProductSpace

/-! ## The minimum principle on discs -/

/-- The circle average of `y ↦ ‖y - c‖²` over `∂B_r(x)` is `‖x - c‖² + r²`. -/
theorem circleAverage_norm_sub_sq (c x : ℂ) (r : ℝ) :
    Real.circleAverage (fun y => ‖y - c‖ ^ 2) x r = ‖x - c‖ ^ 2 + r ^ 2 := by
  set a : ℂ := x - c
  have hh : HarmonicOnNhd (fun y : ℂ => (starRingEnd ℂ a * (y - x)).re) (closedBall x |r|) := fun y _ =>
    AnalyticAt.harmonicAt_re (by fun_prop)
  have hmean := InnerProductSpace.HarmonicOnNhd.circleAverage_eq hh
  simp only [sub_self, mul_zero, zero_re] at hmean
  have hcont : Continuous fun y : ℂ => (starRingEnd ℂ a * (y - x)).re := by fun_prop
  have hci : CircleIntegrable (fun y : ℂ => (starRingEnd ℂ a * (y - x)).re) x r :=
    hcont.continuousOn.circleIntegrable'
  have hci' : CircleIntegrable (fun _ : ℂ => ‖a‖ ^ 2 + r ^ 2) x r :=
    continuousOn_const.circleIntegrable'
  have heq : EqOn (fun y => ‖y - c‖ ^ 2)
      (fun y => (‖a‖ ^ 2 + r ^ 2) + (2 : ℝ) • (starRingEnd ℂ a * (y - x)).re) (sphere x |r|) := by
    intro y hy
    have hyr : ‖y - x‖ = |r| := by simpa [dist_eq_norm] using hy
    have hsplit : y - c = (y - x) + a := by simp [a]
    simp only [smul_eq_mul]
    rw [hsplit, ← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, hyr, sq_abs]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [circleAverage_congr_sphere heq, circleAverage_fun_add hci'
    ((by fun_prop : Continuous fun y : ℂ => (2 : ℝ) • (starRingEnd ℂ a * (y - x)).re).continuousOn.circleIntegrable'),
    circleAverage_const, circleAverage_fun_smul, hmean]
  simp [a]

/-- **Minimum principle on a disc** (AG01 Thm 3.2.2 and Cor 3.2.3, for the disc `B_R(c)`). Let `v` be lower
semicontinuous on `B_R(c)`, with the local super-mean-value property (`M(v; x, r) ≤ v(x)` for all small `r`), and
with `liminf_{y → ξ, y ∈ B_R(c)} v(y) ≥ 0` at every `ξ ∈ ∂B_R(c)`. Then `v ≥ 0` on `B_R(c)`.
Proof: perturb by the strictly subharmonic function `η ‖y - c‖²`; a minimizer `y*` of the lower semicontinuous
extension of `v - η ‖· - c‖²` (by `0 - η ‖· - c‖²` on the circle) to `closedBall c R` lies in `B_R(c)`, and the
super-mean-value inequality at `y*` contradicts `M(‖· - c‖²; y*, r) = ‖y* - c‖² + r²`. -/
theorem nonneg_of_lowerSemicontinuousOn_of_superMean {v : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hlsc : LowerSemicontinuousOn v (ball c R))
    (hmean : ∀ x ∈ ball c R, ∃ ρ > 0, ∀ r ∈ Ioo 0 ρ,
      CircleIntegrable v x r ∧ Real.circleAverage v x r ≤ v x)
    (hbdry : ∀ ξ ∈ sphere c R, ∀ ε > 0, ∀ᶠ y in 𝓝[ball c R] ξ, -ε < v y) :
    ∀ x ∈ ball c R, 0 ≤ v x := by
  intro x₁ hx₁
  by_contra hneg
  push Not at hneg
  have hR : 0 < R := pos_of_mem_ball hx₁
  set K := closedBall c R
  have hBK : ball c R ⊆ K := ball_subset_closedBall
  set w : ℂ → ℝ := (ball c R).indicator v with hw
  set η : ℝ := -v x₁ / (2 * (R ^ 2 + 1))
  have hη : 0 < η := div_pos (by linarith) (by positivity)
  have hηR : η * R ^ 2 < -v x₁ := by
    have : η * (R ^ 2 + 1) = -v x₁ / 2 := by
      simp only [η]; field_simp
    nlinarith
  set W : ℂ → ℝ := fun y => w y - η * ‖y - c‖ ^ 2
  -- `w` is lower semicontinuous on the closed disc
  have hwlsc : LowerSemicontinuousOn w K := by
    intro y hy a ha
    by_cases hyB : y ∈ ball c R
    · have hwy : w y = v y := Set.indicator_of_mem hyB v
      rw [hwy] at ha
      have h1 : ∀ᶠ y' in 𝓝 y, a < v y' := by
        have := hlsc y hyB a ha
        rwa [isOpen_ball.nhdsWithin_eq hyB] at this
      have h2 : ∀ᶠ y' in 𝓝 y, y' ∈ ball c R := isOpen_ball.mem_nhds hyB
      refine nhdsWithin_le_nhds ?_
      filter_upwards [h1, h2] with y' h1' h2'
      rw [hw, Set.indicator_of_mem h2' v]
      exact h1'
    · have hwy : w y = 0 := Set.indicator_of_notMem hyB v
      rw [hwy] at ha
      have hyS : y ∈ sphere c R := by
        rw [← closedBall_sdiff_ball]; exact ⟨hy, hyB⟩
      have h1 := hbdry y hyS (-a) (by linarith)
      rw [eventually_nhdsWithin_iff] at h1
      refine nhdsWithin_le_nhds ?_
      filter_upwards [h1] with y' h1'
      by_cases hy' : y' ∈ ball c R
      · rw [hw, Set.indicator_of_mem hy' v]
        have := h1' hy'
        linarith
      · rw [hw, Set.indicator_of_notMem hy' v]
        exact ha
  have hWlsc : LowerSemicontinuousOn W K := by
    have hc : ContinuousOn (fun y : ℂ => -(η * ‖y - c‖ ^ 2)) K := by fun_prop
    have := hwlsc.add hc.lowerSemicontinuousOn
    simpa [W, sub_eq_add_neg] using this
  obtain ⟨y, hyK, hymin⟩ := hWlsc.exists_isMinOn ⟨c, mem_closedBall_self hR.le⟩ (isCompact_closedBall c R)
  have hWx₁ : W x₁ ≤ v x₁ := by
    have : w x₁ = v x₁ := Set.indicator_of_mem hx₁ v
    simp only [W, this]
    nlinarith [sq_nonneg ‖x₁ - c‖]
  have hyB : y ∈ ball c R := by
    by_contra hyB
    have hwy : w y = 0 := Set.indicator_of_notMem hyB v
    have hyle : ‖y - c‖ ≤ R := by simpa [dist_eq_norm] using hyK
    have h1 : W y ≤ W x₁ := hymin (hBK hx₁)
    have h2 : -(η * R ^ 2) ≤ W y := by
      simp only [W, hwy, zero_sub, neg_le_neg_iff]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hyle 2) hη.le
    linarith
  obtain ⟨ρ, hρ, hρmean⟩ := hmean y hyB
  have hdist : dist y c < R := hyB
  set r : ℝ := min (ρ / 2) ((R - dist y c) / 2)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hrρ : r ∈ Ioo 0 ρ := ⟨hr, lt_of_le_of_lt (min_le_left _ _) (by linarith)⟩
  have hsphB : sphere y r ⊆ ball c R := by
    intro y' hy'
    rw [mem_sphere] at hy'
    rw [mem_ball]
    calc dist y' c ≤ dist y' y + dist y c := dist_triangle _ _ _
      _ = r + dist y c := by rw [hy']
      _ < R := by have := min_le_right (ρ / 2) ((R - dist y c) / 2); linarith
  obtain ⟨hci, hle⟩ := hρmean r hrρ
  have hwyv : w y = v y := Set.indicator_of_mem hyB v
  -- pointwise lower bound on the circle
  have hpt : ∀ y' ∈ sphere y |r|, v y + η * (‖y' - c‖ ^ 2 - ‖y - c‖ ^ 2) ≤ v y' := by
    intro y' hy'
    rw [abs_of_pos hr] at hy'
    have hy'B := hsphB hy'
    have h1 : W y ≤ W y' := hymin (hBK hy'B)
    have hwy' : w y' = v y' := Set.indicator_of_mem hy'B v
    simp only [W, hwyv, hwy'] at h1
    nlinarith
  have hcq : CircleIntegrable (fun y' : ℂ => v y + η * (‖y' - c‖ ^ 2 - ‖y - c‖ ^ 2)) y r :=
    (by fun_prop : Continuous fun y' : ℂ => v y + η * (‖y' - c‖ ^ 2 - ‖y - c‖ ^ 2)).continuousOn.circleIntegrable'
  have hmono := circleAverage_mono hcq hci hpt
  have havg : Real.circleAverage (fun y' : ℂ => v y + η * (‖y' - c‖ ^ 2 - ‖y - c‖ ^ 2)) y r =
      v y + η * r ^ 2 := by
    have hci2 : CircleIntegrable (fun y' : ℂ => ‖y' - c‖ ^ 2) y r :=
      (by fun_prop : Continuous fun y' : ℂ => ‖y' - c‖ ^ 2).continuousOn.circleIntegrable'
    have e1 : (fun y' : ℂ => v y + η * (‖y' - c‖ ^ 2 - ‖y - c‖ ^ 2)) =
        fun y' => (v y - η * ‖y - c‖ ^ 2) + η • ‖y' - c‖ ^ 2 := by
      ext y'; simp only [smul_eq_mul]; ring
    rw [e1, circleAverage_fun_add continuousOn_const.circleIntegrable'
      ((by fun_prop : Continuous fun y' : ℂ => η • ‖y' - c‖ ^ 2).continuousOn.circleIntegrable'),
      circleAverage_const, circleAverage_fun_smul, circleAverage_norm_sub_sq, smul_eq_mul]
    ring
  rw [havg] at hmono
  have : 0 < η * r ^ 2 := by positivity
  linarith

/-! ## Circle averages: measurability, domination, limits -/

/-- A closed disc inside an open set is inside a slightly larger closed disc inside the open set. -/
theorem exists_closedBall_add_subset {U : Set ℂ} (hU : IsOpen U) {x : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : closedBall x r ⊆ U) : ∃ δ > 0, closedBall x (r + δ) ⊆ U := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall x r).exists_cthickening_subset_open hU h
  refine ⟨δ, hδ, ?_⟩
  rwa [cthickening_closedBall hδ.le hr, add_comm] at hsub

/-- The composite of a function lower semicontinuous on `U` with the parametrization of a circle inside `U` is
measurable. -/
theorem LowerSemicontinuousOn.measurable_comp_circleMap {g : ℂ → ℝ} {U : Set ℂ}
    (hg : LowerSemicontinuousOn g U) {x : ℂ} {r : ℝ} (hsph : sphere x |r| ⊆ U) :
    Measurable fun θ => g (circleMap x r θ) := by
  refine LowerSemicontinuous.measurable fun θ a ha => ?_
  have hU : circleMap x r θ ∈ U := hsph (circleMap_mem_sphere' x r θ)
  have h1 := hg _ hU a ha
  have h2 : Tendsto (circleMap x r) (𝓝 θ) (𝓝[U] circleMap x r θ) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_circleMap x r).tendsto θ,
      Eventually.of_forall fun θ' => hsph (circleMap_mem_sphere' x r θ')⟩
  exact h2.eventually h1

/-- A function lower semicontinuous on `U`, bounded below on a circle inside `U` and bounded above there by a circle
integrable function, is circle integrable. -/
theorem LowerSemicontinuousOn.circleIntegrable_of_le {g G : ℂ → ℝ} {U : Set ℂ}
    (hg : LowerSemicontinuousOn g U) {x : ℂ} {r m : ℝ} (hsph : sphere x |r| ⊆ U)
    (hlo : ∀ y ∈ sphere x |r|, m ≤ g y) (hup : ∀ y ∈ sphere x |r|, g y ≤ G y)
    (hG : CircleIntegrable G x r) : CircleIntegrable g x r := by
  have hGm : CircleIntegrable (fun y => |G y| + |m|) x r :=
    hG.abs.add continuousOn_const.circleIntegrable'
  refine IntervalIntegrable.mono_fun' hGm (LowerSemicontinuousOn.measurable_comp_circleMap hg hsph).aestronglyMeasurable ?_
  refine Eventually.of_forall fun θ => ?_
  have hy := circleMap_mem_sphere' x r θ
  have h1 := hlo _ hy
  have h2 := hup _ hy
  simp only [Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> cases abs_cases (G (circleMap x r θ)) <;> cases abs_cases m <;> linarith

/-- **Dominated convergence for circle averages.** -/
theorem tendsto_circleAverage_of_dominated {F : ℕ → ℂ → ℝ} {f G : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hF : ∀ n, CircleIntegrable (F n) c r) (hG : CircleIntegrable G c r)
    (hbound : ∀ n, ∀ y ∈ sphere c |r|, |F n y| ≤ G y)
    (hlim : ∀ y ∈ sphere c |r|, Tendsto (fun n => F n y) atTop (𝓝 (f y))) :
    Tendsto (fun n => Real.circleAverage (F n) c r) atTop (𝓝 (Real.circleAverage f c r)) := by
  simp only [Real.circleAverage_def]
  refine Tendsto.const_smul ?_ _
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun θ => G (circleMap c r θ)) ?_ ?_ hG ?_
  · exact Eventually.of_forall fun n => (hF n).def'.aestronglyMeasurable
  · exact Eventually.of_forall fun n => Eventually.of_forall fun θ _ =>
      hbound n _ (circleMap_mem_sphere' c r θ)
  · exact Eventually.of_forall fun θ _ => hlim _ (circleMap_mem_sphere' c r θ)

/-! ## The Poisson integral of a disc -/

/-- The **Poisson integral** `P_{B_ρ(c)}[φ](x) = M(P(c, x, ·) φ; c, ρ)` of boundary data `φ` on the circle
`∂B_ρ(c)`, with the Poisson kernel `P(c, x, ζ) = (|ζ - c|² - |x - c|²) / |ζ - x|²` (Mathlib `poissonKernel`). -/
noncomputable def discPoissonIntegral (φ : ℂ → ℝ) (c : ℂ) (ρ : ℝ) (x : ℂ) : ℝ :=
  Real.circleAverage (poissonKernel c x • φ) c ρ

section PoissonKernel

variable {c x ζ : ℂ} {ρ : ℝ}

theorem poissonKernel_pos (hx : x ∈ ball c ρ) (hζ : ζ ∈ sphere c ρ) : 0 < poissonKernel c x ζ := by
  rw [poissonKernel_def]
  have hζc : ‖ζ - c‖ = ρ := by simpa [dist_eq_norm] using hζ
  have hxc : ‖x - c‖ < ρ := by simpa [dist_eq_norm] using hx
  have hne : ζ - c - (x - c) ≠ 0 := by
    intro h
    have : ζ = x := by linear_combination h
    rw [this] at hζc
    linarith
  refine div_pos ?_ (by positivity)
  rw [hζc]
  nlinarith [norm_nonneg (x - c)]

/-- Upper bound of the Poisson kernel away from the pole. -/
theorem poissonKernel_le_of_le_norm {δ : ℝ} (hδ : 0 < δ) (hx : x ∈ ball c ρ) (hζ : ζ ∈ sphere c ρ)
    (hd : δ ≤ ‖ζ - x‖) : poissonKernel c x ζ ≤ (ρ ^ 2 - ‖x - c‖ ^ 2) / δ ^ 2 := by
  rw [poissonKernel_def]
  have hζc : ‖ζ - c‖ = ρ := by simpa [dist_eq_norm] using hζ
  have hxc : ‖x - c‖ < ρ := by simpa [dist_eq_norm] using hx
  have e : ζ - c - (x - c) = ζ - x := by ring
  rw [hζc, e]
  apply div_le_div_of_nonneg_left (by nlinarith [norm_nonneg (x - c)]) (by positivity)
  exact pow_le_pow_left₀ hδ.le hd 2

theorem poissonKernel_self (hζ : ζ ∈ sphere c ρ) (hρ : ρ ≠ 0) : poissonKernel c c ζ = 1 := by
  rw [poissonKernel_def]
  have hζc : ‖ζ - c‖ = ρ := by simpa [dist_eq_norm] using hζ
  simp only [sub_self, norm_zero, sub_zero, hζc]
  field_simp
  simp

theorem continuousOn_poissonKernel (hx : x ∈ ball c ρ) :
    ContinuousOn (poissonKernel c x) (sphere c |ρ|) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  refine Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere ?_)
  intro hs
  have h1 : dist x c < ρ := hx
  have h2 : dist x c = |ρ| := hs
  have : ρ ≤ |ρ| := le_abs_self ρ
  have h3 : 0 ≤ dist x c := dist_nonneg
  rw [abs_of_nonneg (by linarith)] at h2
  linarith

theorem continuous_poissonKernel_comp_circleMap (hx : x ∈ ball c ρ) :
    Continuous fun θ => poissonKernel c x (circleMap c ρ θ) :=
  (continuousOn_poissonKernel hx).comp_continuous (continuous_circleMap c ρ)
    (fun θ => circleMap_mem_sphere' c ρ θ)

theorem CircleIntegrable.poissonKernel_smul {φ : ℂ → ℝ} (hφ : CircleIntegrable φ c ρ)
    (hx : x ∈ ball c ρ) : CircleIntegrable (poissonKernel c x • φ) c ρ := by
  have h := IntervalIntegrable.continuousOn_mul hφ
    (continuous_poissonKernel_comp_circleMap hx).continuousOn
  simpa [CircleIntegrable, Pi.smul_apply, smul_eq_mul] using h

theorem circleIntegrable_poissonKernel (hx : x ∈ ball c ρ) : CircleIntegrable (poissonKernel c x) c ρ :=
  (continuousOn_poissonKernel hx).circleIntegrable'

/-- The Poisson kernel has total mass one. -/
theorem circleAverage_poissonKernel (hx : x ∈ ball c ρ) :
    Real.circleAverage (poissonKernel c x) c ρ = 1 := by
  have h := InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul (f := fun _ : ℂ => (1 : ℝ))
    (fun y _ => harmonicAt_const (1 : ℝ)) hx
  have e : (poissonKernel c x • fun _ : ℂ => (1 : ℝ)) = poissonKernel c x := by
    ext ζ; simp
  rwa [e] at h

end PoissonKernel

section PoissonIntegral

variable {φ ψ : ℂ → ℝ} {c x : ℂ} {ρ : ℝ}

/-- The Poisson integral of a circle-integrable function is harmonic in the disc: it is the real part of the
Herglotz–Riesz integral, which is holomorphic off the circle (Mathlib
`analyticOnNhd_circleAverage_herglotzRieszKernel_smul`). -/
theorem harmonicOnNhd_discPoissonIntegral (hφ : CircleIntegrable φ c ρ) :
    HarmonicOnNhd (discPoissonIntegral φ c ρ) (ball c ρ) := by
  have hcm : ∀ θ, circleMap 0 ρ θ + c = circleMap c ρ θ := fun θ => by simp [circleMap, add_comm]
  have hφ0 : CircleIntegrable (fun ζ => φ (ζ + c)) 0 ρ := by
    simpa [CircleIntegrable, hcm] using hφ
  have hφ0' : CircleIntegrable (fun ζ => (φ (ζ + c) : ℂ)) 0 ρ := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hφ0 ⊢
    exact Complex.ofRealCLM.integrable_comp hφ0
  set Φ : ℂ → ℂ := fun w => Real.circleAverage
    (fun ζ => herglotzRieszKernel 0 w ζ • (φ (ζ + c) : ℂ)) 0 ρ
  have hΦ := analyticOnNhd_circleAverage_herglotzRieszKernel_smul hφ0'
  have hnot : ∀ y ∈ ball c ρ, y - c ∉ sphere (0 : ℂ) |ρ| := by
    intro y hy hs
    have h1 : dist y c < ρ := hy
    have h2 : ‖y - c‖ = |ρ| := by simpa using hs
    rw [← dist_eq_norm] at h2
    have h3 : 0 ≤ dist y c := dist_nonneg
    rw [abs_of_nonneg (by linarith)] at h2
    linarith
  have heq : ∀ y ∈ ball c ρ, discPoissonIntegral φ c ρ y = (Φ (y - c)).re := by
    intro y hy
    rw [discPoissonIntegral, ← circleAverage_map_add_const,
      re_circleAverage_herglotzRieszKernel_smul hφ0 (hnot y hy)]
    congr 1
    ext ζ
    simp only [smul_eq_mul, poissonKernel_eq_re_herglotzRieszKernel, Pi.mul_apply, Function.comp_apply,
      herglotzRieszKernel_add_const]
  intro y hy
  have hev : discPoissonIntegral φ c ρ =ᶠ[𝓝 y] fun w => (Φ (w - c)).re :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hy) heq
  rw [harmonicAt_congr_nhds hev]
  have hA : AnalyticAt ℂ (fun w => Φ (w - c)) y := by
    have h1 : AnalyticAt ℂ Φ (y - c) := hΦ (y - c) (hnot y hy)
    have h2 : AnalyticAt ℂ (fun w : ℂ => w - c) y := by fun_prop
    exact h1.comp_of_eq h2 rfl
  exact hA.harmonicAt_re

theorem continuousOn_discPoissonIntegral (hφ : CircleIntegrable φ c ρ) :
    ContinuousOn (discPoissonIntegral φ c ρ) (ball c ρ) := fun y hy =>
  ((harmonicOnNhd_discPoissonIntegral hφ y hy).1.continuousAt).continuousWithinAt

/-- Mean value property of the Poisson integral on circles inside the disc. -/
theorem circleAverage_discPoissonIntegral (hφ : CircleIntegrable φ c ρ) {y : ℂ} {r : ℝ}
    (hsub : closedBall y |r| ⊆ ball c ρ) :
    Real.circleAverage (discPoissonIntegral φ c ρ) y r = discPoissonIntegral φ c ρ y :=
  InnerProductSpace.HarmonicOnNhd.circleAverage_eq fun w hw => harmonicOnNhd_discPoissonIntegral hφ w (hsub hw)

/-- The value of the Poisson integral at the centre is the circle average. -/
theorem discPoissonIntegral_center (hρ : ρ ≠ 0) :
    discPoissonIntegral φ c ρ c = Real.circleAverage φ c ρ := by
  rw [discPoissonIntegral]
  refine circleAverage_congr_sphere fun ζ hζ => ?_
  have hζc : ‖ζ - c‖ = |ρ| := by simpa [dist_eq_norm] using hζ
  have hne : ‖ζ - c‖ ≠ 0 := by rw [hζc]; exact abs_ne_zero.2 hρ
  have hK : poissonKernel c c ζ = 1 := by
    rw [poissonKernel_def]
    simp [hne]
  simp [hK]

theorem discPoissonIntegral_mono (hφ : CircleIntegrable φ c ρ) (hψ : CircleIntegrable ψ c ρ)
    (hx : x ∈ ball c ρ) (hle : ∀ ζ ∈ sphere c ρ, φ ζ ≤ ψ ζ) :
    discPoissonIntegral φ c ρ x ≤ discPoissonIntegral ψ c ρ x := by
  have hρ : 0 < ρ := (dist_nonneg.trans_lt hx)
  refine circleAverage_mono (CircleIntegrable.poissonKernel_smul hφ hx) (CircleIntegrable.poissonKernel_smul hψ hx) fun ζ hζ => ?_
  rw [abs_of_pos hρ] at hζ
  simp only [smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (hle ζ hζ) (poissonKernel_pos hx hζ).le

theorem discPoissonIntegral_const (a : ℝ) (hx : x ∈ ball c ρ) :
    discPoissonIntegral (fun _ => a) c ρ x = a := by
  rw [discPoissonIntegral]
  have e : (poissonKernel c x • fun _ : ℂ => a) = a • poissonKernel c x := by
    ext ζ; simp [mul_comm]
  rw [e, circleAverage_smul, circleAverage_poissonKernel hx, smul_eq_mul, mul_one]

theorem le_discPoissonIntegral {a : ℝ} (hφ : CircleIntegrable φ c ρ) (hx : x ∈ ball c ρ)
    (hle : ∀ ζ ∈ sphere c ρ, a ≤ φ ζ) : a ≤ discPoissonIntegral φ c ρ x := by
  rw [← discPoissonIntegral_const a hx]
  exact discPoissonIntegral_mono continuousOn_const.circleIntegrable' hφ hx hle

/-- **Dominated convergence for Poisson integrals.** -/
theorem tendsto_discPoissonIntegral {Φ : ℕ → ℂ → ℝ} {G : ℂ → ℝ} (hx : x ∈ ball c ρ)
    (hΦ : ∀ n, CircleIntegrable (Φ n) c ρ) (hG : CircleIntegrable G c ρ)
    (hbound : ∀ n, ∀ y ∈ sphere c ρ, |Φ n y| ≤ G y)
    (hlim : ∀ y ∈ sphere c ρ, Tendsto (fun n => Φ n y) atTop (𝓝 (φ y))) :
    Tendsto (fun n => discPoissonIntegral (Φ n) c ρ x) atTop (𝓝 (discPoissonIntegral φ c ρ x)) := by
  have hρ : 0 < ρ := (dist_nonneg.trans_lt hx)
  refine tendsto_circleAverage_of_dominated (fun n => CircleIntegrable.poissonKernel_smul (hΦ n) hx)
    (CircleIntegrable.poissonKernel_smul hG hx) (fun n y hy => ?_) (fun y hy => ?_)
  · rw [abs_of_pos hρ] at hy
    simp only [smul_eq_mul, Pi.mul_apply, abs_mul, abs_of_pos (poissonKernel_pos hx hy)]
    exact mul_le_mul_of_nonneg_left (hbound n y hy) (poissonKernel_pos hx hy).le
  · rw [abs_of_pos hρ] at hy
    simp only [smul_eq_mul, Pi.mul_apply]
    exact (hlim y hy).const_mul _

end PoissonIntegral

/-! ## Boundary values: the Dirichlet problem on a disc -/

section Boundary

variable {φ : ℂ → ℝ} {c : ℂ} {ρ : ℝ}

/-- **Boundary continuity of the Poisson integral** of boundary data continuous on the circle (the Poisson integral
solves the Dirichlet problem on a disc). -/
theorem tendsto_discPoissonIntegral_of_continuousOn (hρ : 0 < ρ) (hφ : ContinuousOn φ (sphere c ρ))
    {ξ : ℂ} (hξ : ξ ∈ sphere c ρ) :
    Tendsto (discPoissonIntegral φ c ρ) (𝓝[ball c ρ] ξ) (𝓝 (φ ξ)) := by
  have hφi : CircleIntegrable φ c ρ := hφ.circleIntegrable hρ.le
  have hφ' : ContinuousOn φ (sphere c |ρ|) := by rwa [abs_of_pos hρ]
  obtain ⟨M, hM⟩ := (isCompact_sphere c ρ).exists_bound_of_continuousOn hφ
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨η, hη, hηφ⟩ := Metric.continuousWithinAt_iff.1 (hφ ξ hξ) (ε / 2) (by positivity)
  set C : ℝ := 16 * (|M| + 1) * ρ / η ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨min (η / 2) (ε / (2 * (C + 1))), by positivity, fun x hx hxξ => ?_⟩
  have hxξ1 : dist x ξ < η / 2 := lt_of_lt_of_le hxξ (min_le_left _ _)
  have hxξ2 : dist x ξ < ε / (2 * (C + 1)) := lt_of_lt_of_le hxξ (min_le_right _ _)
  have hxc : ‖x - c‖ < ρ := by simpa [dist_eq_norm] using hx
  have hξc : ‖ξ - c‖ = ρ := by simpa [dist_eq_norm] using hξ
  set D : ℝ := ρ ^ 2 - ‖x - c‖ ^ 2 with hD
  have hD0 : 0 ≤ D := by nlinarith [norm_nonneg (x - c)]
  have hDle : D ≤ 2 * ρ * dist x ξ := by
    have h1 : ρ - ‖x - c‖ ≤ dist x ξ := by
      rw [dist_eq_norm, ← hξc]
      have := norm_sub_norm_le (ξ - c) (x - c)
      rw [show ξ - c - (x - c) = ξ - x by ring, norm_sub_rev ξ x] at this
      linarith
    have h2 : ρ + ‖x - c‖ ≤ 2 * ρ := by linarith
    have h3 : 0 ≤ ρ - ‖x - c‖ := by linarith
    calc D = (ρ - ‖x - c‖) * (ρ + ‖x - c‖) := by rw [hD]; ring
      _ ≤ dist x ξ * (2 * ρ) := mul_le_mul h1 h2 (by positivity) dist_nonneg
      _ = 2 * ρ * dist x ξ := by ring
  -- the difference as a circle average
  have hKc := continuousOn_poissonKernel hx
  have hdiff : discPoissonIntegral φ c ρ x - φ ξ =
      Real.circleAverage (fun ζ => poissonKernel c x ζ * (φ ζ - φ ξ)) c ρ := by
    have e : (fun ζ => poissonKernel c x ζ * (φ ζ - φ ξ)) =
        fun ζ => (poissonKernel c x • φ) ζ - (φ ξ • poissonKernel c x) ζ := by
      ext ζ
      change poissonKernel c x ζ * (φ ζ - φ ξ) = poissonKernel c x ζ * φ ζ - φ ξ * poissonKernel c x ζ
      ring
    have hKi : CircleIntegrable (φ ξ • poissonKernel c x) c ρ :=
      CircleIntegrable.const_smul (circleIntegrable_poissonKernel hx)
    rw [e, circleAverage_fun_sub (CircleIntegrable.poissonKernel_smul hφi hx) hKi, circleAverage_smul,
      circleAverage_poissonKernel hx, smul_eq_mul (φ ξ) (1 : ℝ), mul_one, discPoissonIntegral]
  rw [Real.dist_eq, hdiff]
  have hint1 : CircleIntegrable |fun ζ => poissonKernel c x ζ * (φ ζ - φ ξ)| c ρ :=
    (hKc.mul (hφ'.sub continuousOn_const)).abs.circleIntegrable'
  have hint2 : CircleIntegrable (fun ζ => ε / 2 * poissonKernel c x ζ + 8 * |M| * D / η ^ 2) c ρ :=
    ((continuousOn_const.mul hKc).add continuousOn_const).circleIntegrable'
  have hpt : ∀ ζ ∈ sphere c |ρ|, |fun ζ => poissonKernel c x ζ * (φ ζ - φ ξ)| ζ ≤
      ε / 2 * poissonKernel c x ζ + 8 * |M| * D / η ^ 2 := by
    intro ζ hζ
    rw [abs_of_pos hρ] at hζ
    have hK := poissonKernel_pos hx hζ
    have hT : 0 ≤ 8 * |M| * D / η ^ 2 := by positivity
    change |poissonKernel c x ζ * (φ ζ - φ ξ)| ≤ _
    rw [abs_mul, abs_of_pos hK]
    by_cases hζξ : dist ζ ξ < η
    · have := hηφ hζ hζξ
      rw [Real.dist_eq] at this
      have h5 : poissonKernel c x ζ * |φ ζ - φ ξ| ≤ poissonKernel c x ζ * (ε / 2) :=
        mul_le_mul_of_nonneg_left this.le hK.le
      linarith
    · push Not at hζξ
      have hfar : η / 2 ≤ ‖ζ - x‖ := by
        have := dist_triangle ζ x ξ
        rw [dist_eq_norm ζ x] at this
        linarith
      have hKle := poissonKernel_le_of_le_norm (by positivity) hx hζ hfar
      have hφd : |φ ζ - φ ξ| ≤ 2 * |M| := by
        have h1 := hM ζ hζ
        have h2 := hM ξ hξ
        rw [Real.norm_eq_abs] at h1 h2
        calc |φ ζ - φ ξ| ≤ |φ ζ| + |φ ξ| := abs_sub _ _
          _ ≤ 2 * |M| := by linarith [le_abs_self M]
      have e : (ρ ^ 2 - ‖x - c‖ ^ 2) / (η / 2) ^ 2 = 4 * D / η ^ 2 := by
        rw [hD]; field_simp; ring
      rw [e] at hKle
      have h4 : poissonKernel c x ζ * |φ ζ - φ ξ| ≤ 4 * D / η ^ 2 * (2 * |M|) :=
        mul_le_mul hKle hφd (abs_nonneg _) (by positivity)
      have e2 : 4 * D / η ^ 2 * (2 * |M|) = 8 * |M| * D / η ^ 2 := by ring
      nlinarith
  calc |Real.circleAverage (fun ζ => poissonKernel c x ζ * (φ ζ - φ ξ)) c ρ|
      ≤ Real.circleAverage |fun ζ => poissonKernel c x ζ * (φ ζ - φ ξ)| c ρ :=
        abs_circleAverage_le_circleAverage_abs
    _ ≤ Real.circleAverage (fun ζ => ε / 2 * poissonKernel c x ζ + 8 * |M| * D / η ^ 2) c ρ :=
        circleAverage_mono hint1 hint2 hpt
    _ = ε / 2 + 8 * |M| * D / η ^ 2 := by
        rw [circleAverage_fun_add (show CircleIntegrable (fun ζ => ε / 2 * poissonKernel c x ζ) c ρ from
          (continuousOn_const.mul hKc).circleIntegrable') continuousOn_const.circleIntegrable',
          circleAverage_const]
        have e : (fun ζ => ε / 2 * poissonKernel c x ζ) = fun ζ => (ε / 2) • poissonKernel c x ζ := rfl
        rw [e, circleAverage_fun_smul, circleAverage_poissonKernel hx, smul_eq_mul, mul_one]
    _ < ε := by
        have h1 : 8 * |M| * D / η ^ 2 ≤ C * dist x ξ := by
          rw [hC, div_mul_eq_mul_div]
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith [abs_nonneg M]
        have h2 : C * dist x ξ ≤ C * (ε / (2 * (C + 1))) := mul_le_mul_of_nonneg_left hxξ2.le hC0
        have h3 : C * (ε / (2 * (C + 1))) < ε / 2 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        linarith

end Boundary

/-! ## Approximation of lower semicontinuous functions from below -/

/-- **Inf-convolution** (Baire): a function lower semicontinuous on a nonempty compact set `K` is the pointwise limit
on `K` of continuous functions `ψ_n ≤ u` on `K`, uniformly bounded below; `ψ_n(y) = inf_{w ∈ K} (u(w) + n |y - w|)`. -/
theorem exists_continuous_tendsto_of_lowerSemicontinuousOn {K : Set ℂ} (hK : IsCompact K)
    (hKne : K.Nonempty) {u : ℂ → ℝ} (hu : LowerSemicontinuousOn u K) :
    ∃ ψ : ℕ → ℂ → ℝ, (∀ n, Continuous (ψ n)) ∧ (∀ n, ∀ y ∈ K, ψ n y ≤ u y) ∧
      (∃ m : ℝ, ∀ n y, m ≤ ψ n y) ∧ ∀ y ∈ K, Tendsto (fun n => ψ n y) atTop (𝓝 (u y)) := by
  obtain ⟨a, haK, hamin⟩ := hu.exists_isMinOn hKne hK
  have : Nonempty K := ⟨⟨a, haK⟩⟩
  set m := u a
  have hm : ∀ w ∈ K, m ≤ u w := fun w hw => hamin hw
  set ψ : ℕ → ℂ → ℝ := fun n y => ⨅ w : K, (u w + n * dist y w) with hψ
  have hbdd : ∀ (n : ℕ) (y : ℂ), BddBelow (range fun w : K => u w + n * dist y w) := fun n y =>
    ⟨m, by rintro _ ⟨w, rfl⟩; have := hm w w.2; have : (0 : ℝ) ≤ n * dist y w := (by positivity); linarith⟩
  have hlow : ∀ n y, m ≤ ψ n y := fun n y =>
    le_ciInf fun w => by have := hm w w.2; have : (0 : ℝ) ≤ n * dist y w := (by positivity); linarith
  have hle : ∀ n, ∀ y ∈ K, ψ n y ≤ u y := fun n y hy => by
    have := ciInf_le (hbdd n y) ⟨y, hy⟩
    simpa using this
  have hlip : ∀ (n : ℕ) (y y' : ℂ), ψ n y ≤ ψ n y' + n * dist y y' := by
    intro n y y'
    have : ψ n y - n * dist y y' ≤ ψ n y' := by
      refine le_ciInf fun w => ?_
      have h1 := ciInf_le (hbdd n y) w
      have h2 : dist y w ≤ dist y y' + dist y' w := dist_triangle _ _ _
      have h3 : (n : ℝ) * dist y w ≤ n * dist y y' + n * dist y' w := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg n)
      simp only [ψ] at h1 ⊢
      linarith
    linarith
  refine ⟨ψ, fun n => ?_, hle, ⟨m, hlow⟩, fun y hy => ?_⟩
  · exact (LipschitzWith.of_le_add_mul (n : NNReal) fun y y' => by simpa using hlip n y y').continuous
  · refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => Eventually.of_forall fun n =>
      (hle n y hy).trans_lt hb⟩
    set b' := (b + u y) / 2
    have hbb' : b < b' := by simp only [b']; linarith
    have hb' : b' < u y := by simp only [b']; linarith
    obtain ⟨η, hη, hball⟩ := Metric.mem_nhdsWithin_iff.1 (hu y hy b' hb')
    obtain ⟨N, hN⟩ := exists_nat_ge ((u y - m) / η)
    refine eventually_atTop.2 ⟨N + 1, fun n hn => ?_⟩
    have hnη : u y - m < n * η := by
      have hNn : (N : ℝ) < n := by exact_mod_cast (show N < n by omega)
      have h1 : (u y - m) / η < n := lt_of_le_of_lt hN hNn
      rwa [div_lt_iff₀ hη] at h1
    refine hbb'.trans_le (le_ciInf fun w => ?_)
    by_cases hw : dist (w : ℂ) y < η
    · have h1 : b' < u w := hball ⟨mem_ball.2 hw, w.2⟩
      have : (0 : ℝ) ≤ n * dist y w := by positivity
      linarith
    · push Not at hw
      have := hm w w.2
      have h2 : (n : ℝ) * η ≤ n * dist y w := by
        rw [dist_comm] at hw; exact mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg n)
      linarith

/-! ## Comparison with Poisson integrals -/

section Comparison

variable {U : Set ℂ} {u : ℂ → ℝ}

/-- **Comparison with the Poisson integral of continuous minorants** (minimum principle): if `u` is lower
semicontinuous on `U` with the local super-mean-value property, `closedBall c ρ ⊆ U`, and `φ` is continuous on
`∂B_ρ(c)` with `φ ≤ u` there, then `P_{B_ρ(c)}[φ] ≤ u` in `B_ρ(c)`. -/
theorem discPoissonIntegral_le_of_continuousOn (hlsc : LowerSemicontinuousOn u U)
    (hloc : ∀ x ∈ U, ∃ r₀ > 0, ∀ r ∈ Ioo 0 r₀, CircleIntegrable u x r ∧ Real.circleAverage u x r ≤ u x)
    {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hsub : closedBall c ρ ⊆ U) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ (sphere c ρ)) (hle : ∀ ζ ∈ sphere c ρ, φ ζ ≤ u ζ) :
    ∀ x ∈ ball c ρ, discPoissonIntegral φ c ρ x ≤ u x := by
  have hφi : CircleIntegrable φ c ρ := hφ.circleIntegrable hρ.le
  have hPc := continuousOn_discPoissonIntegral hφi
  have hbU : ball c ρ ⊆ U := ball_subset_closedBall.trans hsub
  have h1 : LowerSemicontinuousOn (fun y => u y - discPoissonIntegral φ c ρ y) (ball c ρ) := by
    have := (hlsc.mono hbU).add hPc.neg.lowerSemicontinuousOn
    simpa [sub_eq_add_neg] using this
  have h2 : ∀ y ∈ ball c ρ, ∃ r₀ > 0, ∀ r ∈ Ioo 0 r₀,
      CircleIntegrable (fun y => u y - discPoissonIntegral φ c ρ y) y r ∧
      Real.circleAverage (fun y => u y - discPoissonIntegral φ c ρ y) y r ≤
        u y - discPoissonIntegral φ c ρ y := by
    intro y hy
    obtain ⟨r₀, hr₀, hmean⟩ := hloc y (hbU hy)
    have hyc : dist y c < ρ := hy
    refine ⟨min r₀ (ρ - dist y c), lt_min hr₀ (by linarith), fun r hr => ?_⟩
    have hr0 : 0 < r := hr.1
    have hrr₀ : r < r₀ := lt_of_lt_of_le hr.2 (min_le_left _ _)
    have hrρ : r < ρ - dist y c := lt_of_lt_of_le hr.2 (min_le_right _ _)
    obtain ⟨hui, hum⟩ := hmean r ⟨hr0, hrr₀⟩
    have hsub' : closedBall y |r| ⊆ ball c ρ := by
      rw [abs_of_pos hr0]; exact closedBall_subset_ball' (by linarith)
    have hPi : CircleIntegrable (discPoissonIntegral φ c ρ) y r :=
      (hPc.mono (sphere_subset_closedBall.trans hsub')).circleIntegrable'
    refine ⟨hui.sub hPi, ?_⟩
    rw [circleAverage_fun_sub hui hPi, circleAverage_discPoissonIntegral hφi hsub']
    linarith
  have h3 : ∀ ξ ∈ sphere c ρ, ∀ ε > 0, ∀ᶠ y in 𝓝[ball c ρ] ξ,
      -ε < u y - discPoissonIntegral φ c ρ y := by
    intro ξ hξ ε hε
    have hξU : ξ ∈ U := hsub (sphere_subset_closedBall hξ)
    have e1 : ∀ᶠ y in 𝓝[ball c ρ] ξ, u ξ - ε / 2 < u y :=
      nhdsWithin_mono ξ hbU (hlsc ξ hξU _ (by linarith))
    have e2 : ∀ᶠ y in 𝓝[ball c ρ] ξ, discPoissonIntegral φ c ρ y < φ ξ + ε / 2 :=
      (tendsto_discPoissonIntegral_of_continuousOn hρ hφ hξ).eventually (gt_mem_nhds (by linarith))
    filter_upwards [e1, e2] with y hy1 hy2
    have := hle ξ hξ
    linarith
  intro x hx
  have := nonneg_of_lowerSemicontinuousOn_of_superMean h1 h2 h3 x hx
  linarith

/-- Continuous approximation from below on a circle, with a uniform bound, of a function lower semicontinuous on
`U ⊇ ∂B_ρ(c)`. -/
theorem exists_continuous_approx_sphere (hlsc : LowerSemicontinuousOn u U) {c : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsub : sphere c ρ ⊆ U) :
    ∃ ψ : ℕ → ℂ → ℝ, ∃ m : ℝ, (∀ n, Continuous (ψ n)) ∧ (∀ n, ∀ y ∈ sphere c ρ, ψ n y ≤ u y) ∧
      (∀ n, ∀ y ∈ sphere c ρ, |ψ n y| ≤ |u y| + |m|) ∧
      ∀ y ∈ sphere c ρ, Tendsto (fun n => ψ n y) atTop (𝓝 (u y)) := by
  obtain ⟨ψ, hc, hle, ⟨m, hm⟩, hlim⟩ := exists_continuous_tendsto_of_lowerSemicontinuousOn
    (isCompact_sphere c ρ) (NormedSpace.sphere_nonempty.2 hρ) (hlsc.mono hsub)
  refine ⟨ψ, m, hc, hle, fun n y hy => ?_, hlim⟩
  have h1 := hm n y
  have h2 := hle n y hy
  rw [abs_le]
  constructor <;> cases abs_cases (u y) <;> cases abs_cases m <;> linarith

/-- **The local super-mean-value property is global** (AG01 Thm 3.2.2, finite-valued form): a function lower
semicontinuous on `U` with the local super-mean-value property satisfies `M(u; x, r) ≤ u(x)` for every closed disc
`closedBall x r ⊆ U` on whose boundary it is circle integrable. -/
theorem circleAverage_le_of_localSuperMean (hlsc : LowerSemicontinuousOn u U)
    (hloc : ∀ x ∈ U, ∃ r₀ > 0, ∀ r ∈ Ioo 0 r₀, CircleIntegrable u x r ∧ Real.circleAverage u x r ≤ u x)
    {x : ℂ} {r : ℝ} (hr : 0 < r) (hsub : closedBall x r ⊆ U) (hui : CircleIntegrable u x r) :
    Real.circleAverage u x r ≤ u x := by
  obtain ⟨ψ, m, hψc, hψle, hψb, hψlim⟩ :=
    exists_continuous_approx_sphere hlsc hr.le (sphere_subset_closedBall.trans hsub)
  have hn : ∀ n, Real.circleAverage (ψ n) x r ≤ u x := fun n => by
    rw [← discPoissonIntegral_center hr.ne']
    exact discPoissonIntegral_le_of_continuousOn hlsc hloc hr hsub (hψc n).continuousOn (hψle n) x
      (mem_ball_self hr)
  have hlim := tendsto_circleAverage_of_dominated (F := ψ) (G := fun y => |u y| + |m|)
    (fun n => (hψc n).continuousOn.circleIntegrable') (hui.abs.add continuousOn_const.circleIntegrable')
    (fun n y hy => hψb n y (by rwa [abs_of_pos hr] at hy))
    (fun y hy => hψlim y (by rwa [abs_of_pos hr] at hy))
  exact le_of_tendsto' hlim hn

/-- **Poisson inequality** (eq:superharmonic-poisson-inequality): for `u` lower semicontinuous on `U` with the local
super-mean-value property and `closedBall c ρ ⊆ U`, `P_{B_ρ(c)}[u] ≤ u` in `B_ρ(c)`. -/
theorem discPoissonIntegral_le (hlsc : LowerSemicontinuousOn u U)
    (hloc : ∀ x ∈ U, ∃ r₀ > 0, ∀ r ∈ Ioo 0 r₀, CircleIntegrable u x r ∧ Real.circleAverage u x r ≤ u x)
    {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hsub : closedBall c ρ ⊆ U) (hui : CircleIntegrable u c ρ) :
    ∀ x ∈ ball c ρ, discPoissonIntegral u c ρ x ≤ u x := by
  intro x hx
  obtain ⟨ψ, m, hψc, hψle, hψb, hψlim⟩ :=
    exists_continuous_approx_sphere hlsc hρ.le (sphere_subset_closedBall.trans hsub)
  have hn : ∀ n, discPoissonIntegral (ψ n) c ρ x ≤ u x := fun n =>
    discPoissonIntegral_le_of_continuousOn hlsc hloc hρ hsub (hψc n).continuousOn (hψle n) x hx
  have hlim := tendsto_discPoissonIntegral (φ := u) (Φ := ψ) (G := fun y => |u y| + |m|) hx
    (fun n => (hψc n).continuousOn.circleIntegrable') (hui.abs.add continuousOn_const.circleIntegrable')
    hψb hψlim
  exact le_of_tendsto' hlim hn

/-- **Lower boundary limits of the Poisson integral**: for `u` lower semicontinuous on `U ⊇ ∂B_ρ(c)` and circle
integrable on `∂B_ρ(c)`, `liminf_{y → ξ, y ∈ B_ρ(c)} P_{B_ρ(c)}[u](y) ≥ u(ξ)` at every `ξ ∈ ∂B_ρ(c)`. -/
theorem eventually_lt_discPoissonIntegral (hlsc : LowerSemicontinuousOn u U) {c : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hsub : sphere c ρ ⊆ U) (hui : CircleIntegrable u c ρ) {ξ : ℂ} (hξ : ξ ∈ sphere c ρ)
    {a : ℝ} (ha : a < u ξ) : ∀ᶠ y in 𝓝[ball c ρ] ξ, a < discPoissonIntegral u c ρ y := by
  obtain ⟨ψ, m, hψc, hψle, -, hψlim⟩ := exists_continuous_approx_sphere hlsc hρ.le hsub
  obtain ⟨n, hn⟩ := ((hψlim ξ hξ).eventually (lt_mem_nhds ha)).exists
  have e1 := (tendsto_discPoissonIntegral_of_continuousOn hρ (hψc n).continuousOn hξ).eventually
    (lt_mem_nhds hn)
  filter_upwards [e1, self_mem_nhdsWithin] with y hy hyb
  exact hy.trans_le (discPoissonIntegral_mono (hψc n).continuousOn.circleIntegrable' hui hyb (hψle n))

end Comparison

end HarmonicBalls
