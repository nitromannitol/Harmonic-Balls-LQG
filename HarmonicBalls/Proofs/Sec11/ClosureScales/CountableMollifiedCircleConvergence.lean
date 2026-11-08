import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.CountableCircleDecoder
import HarmonicBalls.Proofs.Sec11.ClosureScales.MollifiedCircleGaussianL2

/-!
# Countable family of mollified circle pairings: deterministic scales and almost sure convergence

Written argument: `notes/sec11-proof/sec11-proof-r10.tex`, lines 1304-1312 (audited in `AUDIT-r9.md` 931-957 and
`AUDIT-r10.md` 110). For a literal mollifier `ρ` (`IsLiteralMollifier`) and a countable family `q : I → CircleDomain`
of coded circles `(r_i, w_i)`, the scales `countableCircleScale hρ q i n` are built from `ρ` and `q` only: they are
positive, strictly decreasing in `n`, and tend to `0`.

For every whole-plane GFF `(P, hC, hcirc)` (`IsWholePlaneGFF`), the squared `L²(P)` distance between
`⟨h, φ_ε^{(w_i, r_i)}⟩` and `h_{r_i}(w_i)` is the deterministic covariance expression `circleErr`, which is at most
`2^(-4n)` at `ε = countableCircleScale hρ q i n`. Chebyshev's inequality bounds `P(|error| ≥ 2^(-n))` by `2^(-2n)`,
which is summable; the first Borel-Cantelli lemma and a countable union over the circles give a measurable event `S`
with `P Sᶜ = 0` on which `⟨h, φ_ε⟩ → h_{r_i}(w_i)` for every `i`.

No convergence, covariance-rate, decoder, representation or density premise is used.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Topology Metric Set

universe u

/-- The deterministic squared `L²` error of the literal mollified circle pairing, as the covariance expression of the
whole-plane kernel: `Cov(⟨h,φ_e⟩,⟨h,φ_e⟩) - 2 Cov(⟨h,φ_e⟩,h_r(w)) + Cov(h_r(w),h_r(w))`. It depends only on
`ρ, r, w, e`: no Gaussian field enters. -/
noncomputable def circleErr (rho : ℂ → ℝ) (r : ℝ) (w : ℂ) (e : ℝ) : ℝ :=
  wholePlaneGFFCov (.pairing (circleMollifier rho w r e)) (.pairing (circleMollifier rho w r e))
    - 2 * wholePlaneGFFCov (.pairing (circleMollifier rho w r e)) (.circle r w)
    + wholePlaneGFFCov (.circle r w) (.circle r w)

/-- The level `2^(-4n)` of the `n`-th error bound, written as the natural power `(1/16)^n`. -/
noncomputable def circleLevel (n : ℕ) : ℝ :=
  (1 / 16 : ℝ) ^ n

lemma circleLevel_pos (n : ℕ) : 0 < circleLevel n :=
  pow_pos (by norm_num) n

lemma two_zpow_neg_four_mul (n : ℕ) : (2 : ℝ) ^ (-(4 * (n : ℤ))) = circleLevel n := by
  unfold circleLevel
  rw [show -(4 * (n : ℤ)) = (-4 : ℤ) * (n : ℤ) by ring, zpow_mul, zpow_natCast]
  norm_num

/-- **Deterministic covariance identity.** For a whole-plane GFF and a scale `e > 0`, the squared `L²(P)` distance
between the mollified pairing and the circle average equals `circleErr ρ r w e`, a number that does not depend on the
probability space or on the realization. -/
lemma integral_sq_circleMollifier_sub_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {r : ℝ} (hr : 0 < r) (w : ℂ) {e : ℝ} (he : 0 < e) :
    ∫ ξ, (hC ξ (circleMollifier rho w r e) - hcirc ξ r w) ^ 2 ∂P = circleErr rho r w e := by
  unfold circleErr
  have hadmC : GFFObservable.IsAdmissible (.pairing (circleMollifier rho w r e)) :=
    isTestFunction_circleMollifier (w := w) hρ hr he
  have hadmY : GFFObservable.IsAdmissible (.circle r w) := hr
  have hX : MemLp (fun ξ => hC ξ (circleMollifier rho w r e)) 2 P :=
    (hGFF.isGaussianProcess.hasGaussianLaw_eval
      (⟨.pairing (circleMollifier rho w r e), hadmC⟩ : GFFObservable.Admissible)).memLp_two
  have hY : MemLp (fun ξ => hcirc ξ r w) 2 P := (hGFF.hasGaussianLaw_circle hr w).memLp_two
  have hmeanX : ∫ ξ, hC ξ (circleMollifier rho w r e) ∂P = 0 := hGFF.integral_eq_zero _ hadmC
  have hmeanY : ∫ ξ, hcirc ξ r w ∂P = 0 := hGFF.integral_eq_zero _ hadmY
  have h1 : covariance (fun ξ => hC ξ (circleMollifier rho w r e))
      (fun ξ => hC ξ (circleMollifier rho w r e)) P =
      wholePlaneGFFCov (.pairing (circleMollifier rho w r e)) (.pairing (circleMollifier rho w r e)) :=
    hGFF.covariance_eq _ _ hadmC hadmC
  have h2 : covariance (fun ξ => hC ξ (circleMollifier rho w r e)) (fun ξ => hcirc ξ r w) P =
      wholePlaneGFFCov (.pairing (circleMollifier rho w r e)) (.circle r w) :=
    hGFF.covariance_eq _ _ hadmC hadmY
  have h3 : covariance (fun ξ => hcirc ξ r w) (fun ξ => hcirc ξ r w) P =
      wholePlaneGFFCov (.circle r w) (.circle r w) :=
    hGFF.covariance_eq _ _ hadmY hadmY
  rw [integral_sq_sub_eq_covariance hX hY hmeanX hmeanY, h1, h2, h3]

/-- The deterministic error tends to `0` as the scale decreases to `0`, by the deterministic covariance limits. -/
lemma tendsto_circleErr {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {r : ℝ} (hr : 0 < r) (w : ℂ) :
    Tendsto (circleErr rho r w) (𝓝[>] 0) (𝓝 0) := by
  have hΦ := tendsto_wholePlaneGFFCov_pairing_pairing hρ w hr
  have hΨ := tendsto_wholePlaneGFFCov_pairing_circle hρ w hr
  have hconst : Tendsto (fun _ : ℝ => wholePlaneGFFCov (.circle r w) (.circle r w)) (𝓝[>] 0)
      (𝓝 (wholePlaneGFFCov (.circle r w) (.circle r w))) := tendsto_const_nhds
  have hlim := (hΦ.sub (hΨ.const_mul 2)).add hconst
  have h0 : wholePlaneGFFCov (.circle r w) (.circle r w) - 2 * wholePlaneGFFCov (.circle r w) (.circle r w) +
      wholePlaneGFFCov (.circle r w) (.circle r w) = 0 := by ring
  rw [h0] at hlim
  exact hlim

/-- For every level `c > 0` there is a radius `δ ∈ (0, 1]` below which the deterministic error is smaller than `c`. -/
lemma exists_circleErr_lt {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {r : ℝ} (hr : 0 < r) (w : ℂ)
    {c : ℝ} (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ e : ℝ, 0 < e → e < δ → circleErr rho r w e < c := by
  have hev : {e : ℝ | circleErr rho r w e < c} ∈ 𝓝[>] (0 : ℝ) :=
    (tendsto_order.1 (tendsto_circleErr hρ hr w)).2 c hc
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨min u 1, lt_min hu0 zero_lt_one, min_le_right _ _, fun e he0 he => ?_⟩
  exact hsub (show e ∈ Ioo (0 : ℝ) u from ⟨he0, lt_of_lt_of_le he (min_le_left _ _)⟩)

/-- The radius chosen at level `n` for the `i`-th coded circle `q i = (r_i, w_i)`: the radius of
`exists_circleErr_lt` at level `circleLevel n`. It is a function of `ρ, q, i, n` only, fixed before any probability
space is given. -/
noncomputable def circleThreshold {I : Type*} {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) (q : I → CircleDomain)
    (i : I) (n : ℕ) : ℝ :=
  Classical.choose (exists_circleErr_lt hρ (q i).property (q i).val.2 (circleLevel_pos n))

lemma circleThreshold_spec {I : Type*} {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) (q : I → CircleDomain)
    (i : I) (n : ℕ) :
    0 < circleThreshold hρ q i n ∧ circleThreshold hρ q i n ≤ 1 ∧
      ∀ e : ℝ, 0 < e → e < circleThreshold hρ q i n →
        circleErr rho (q i).val.1 (q i).val.2 e < circleLevel n :=
  Classical.choose_spec (exists_circleErr_lt hρ (q i).property (q i).val.2 (circleLevel_pos n))

/-- The running minimum `min (f 0) ⋯ (f n)` of a real sequence. -/
noncomputable def circlePrefixMin (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => f 0
  | n + 1 => min (circlePrefixMin f n) (f (n + 1))

lemma circlePrefixMin_pos {f : ℕ → ℝ} (hf : ∀ n, 0 < f n) (n : ℕ) : 0 < circlePrefixMin f n := by
  induction n with
  | zero => exact hf 0
  | succ n ih => exact lt_min ih (hf (n + 1))

lemma circlePrefixMin_le {f : ℕ → ℝ} {n k : ℕ} (hk : k ≤ n) : circlePrefixMin f n ≤ f k := by
  induction n with
  | zero =>
    obtain rfl : k = 0 := by omega
    exact le_rfl
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · exact (min_le_left _ _).trans (ih (by omega))
    · obtain rfl : k = n + 1 := by omega
      exact min_le_right _ _

/-- **The countable family of deterministic scales.** For `i : I`, the sequence `n ↦ ε_{i,n}` is the running minimum of
the radii `circleThreshold hρ q i k` (`k ≤ n`), divided by `n + 2`. It is built from `ρ` and `q` only. -/
noncomputable def countableCircleScale {I : Type*} {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho)
    (q : I → CircleDomain) (i : I) (n : ℕ) : ℝ :=
  circlePrefixMin (fun k => circleThreshold hρ q i k) n / ((n : ℝ) + 2)

lemma circleThreshold_pos {I : Type*} {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) (q : I → CircleDomain)
    (i : I) (n : ℕ) : 0 < circleThreshold hρ q i n :=
  (circleThreshold_spec hρ q i n).1

lemma countableCircleScale_pos {I : Type*} {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) (q : I → CircleDomain)
    (i : I) (n : ℕ) : 0 < countableCircleScale hρ q i n :=
  div_pos (circlePrefixMin_pos (fun k => circleThreshold_pos hρ q i k) n) (by positivity)

lemma countableCircleScale_lt_threshold {I : Type*} {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho)
    (q : I → CircleDomain) (i : I) (n : ℕ) :
    countableCircleScale hρ q i n < circleThreshold hρ q i n := by
  have hm := circlePrefixMin_pos (fun k => circleThreshold_pos hρ q i k) n
  have hle : circlePrefixMin (fun k => circleThreshold hρ q i k) n ≤ circleThreshold hρ q i n :=
    circlePrefixMin_le (f := fun k => circleThreshold hρ q i k) (k := n) le_rfl
  have h2 : (1 : ℝ) < (n : ℝ) + 2 := by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  calc countableCircleScale hρ q i n
      < circlePrefixMin (fun k => circleThreshold hρ q i k) n := div_lt_self hm h2
    _ ≤ circleThreshold hρ q i n := hle

lemma countableCircleScale_strictAnti {I : Type*} {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho)
    (q : I → CircleDomain) (i : I) : StrictAnti (countableCircleScale hρ q i) := by
  refine strictAnti_nat_of_succ_lt fun n => ?_
  have hm := circlePrefixMin_pos (fun k => circleThreshold_pos hρ q i k) n
  have hmono : circlePrefixMin (fun k => circleThreshold hρ q i k) (n + 1) ≤
      circlePrefixMin (fun k => circleThreshold hρ q i k) n := min_le_left _ _
  unfold countableCircleScale
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hmono (by positivity : (0 : ℝ) ≤ (n : ℝ) + 2)]

lemma countableCircleScale_tendsto {I : Type*} {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho)
    (q : I → CircleDomain) (i : I) : Tendsto (countableCircleScale hρ q i) atTop (𝓝[>] 0) := by
  have hbound : ∀ n : ℕ, countableCircleScale hρ q i n ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have hm1 : circlePrefixMin (fun k => circleThreshold hρ q i k) n ≤ 1 :=
      (circlePrefixMin_le (f := fun k => circleThreshold hρ q i k) (k := 0) (Nat.zero_le n)).trans
        (circleThreshold_spec hρ q i 0).2.1
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    unfold countableCircleScale
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hm1 (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  rw [tendsto_nhdsWithin_iff]
  exact ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (countableCircleScale_pos hρ q i n).le) hbound,
    Eventually.of_forall fun n => countableCircleScale_pos hρ q i n⟩

/-- **The scales of the countable family.** They are positive, strictly decreasing in `n` for each `i`, and tend to `0`
through positive values; they are functions of `ρ` and `q` only. -/
theorem countableCircleScale_spec {I : Type*} {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho)
    (q : I → CircleDomain) :
    (∀ (i : I) (n : ℕ), 0 < countableCircleScale hρ q i n) ∧
      (∀ i : I, StrictAnti (countableCircleScale hρ q i)) ∧
      ∀ i : I, Tendsto (countableCircleScale hρ q i) atTop (𝓝[>] 0) :=
  ⟨fun i n => countableCircleScale_pos hρ q i n, fun i => countableCircleScale_strictAnti hρ q i,
    fun i => countableCircleScale_tendsto hρ q i⟩

/-- Chebyshev's inequality for the squared error, in lintegral form (valid for every measure): if `∫ Y² ≤ 2^(-4n)`,
then `P{(1/4)^n ≤ Y²} ≤ (1/4)^n`, that is `P{|Y| ≥ 2^(-n)} ≤ 2^(-2n)`. -/
lemma measure_sq_ge_le_ofReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ} (hY : Measurable Y)
    (hint : Integrable (fun ξ => Y ξ ^ 2) P) {n : ℕ} (hbound : ∫ ξ, Y ξ ^ 2 ∂P ≤ circleLevel n) :
    P {ξ | (1 / 4 : ℝ) ^ n ≤ Y ξ ^ 2} ≤ ENNReal.ofReal ((1 / 4 : ℝ) ^ n) := by
  have hnn : 0 ≤ᵐ[P] fun ξ => Y ξ ^ 2 := ae_of_all _ fun ξ => sq_nonneg _
  have hmeas2 : Measurable fun ξ => ENNReal.ofReal (Y ξ ^ 2) := (hY.pow_const 2).ennreal_ofReal
  have hmark : ENNReal.ofReal ((1 / 4 : ℝ) ^ n) * P {ξ | (1 / 4 : ℝ) ^ n ≤ Y ξ ^ 2} ≤
      ∫⁻ ξ, ENNReal.ofReal (Y ξ ^ 2) ∂P := by
    have hset : {ξ | ENNReal.ofReal ((1 / 4 : ℝ) ^ n) ≤ ENNReal.ofReal (Y ξ ^ 2)} =
        {ξ | (1 / 4 : ℝ) ^ n ≤ Y ξ ^ 2} := by
      ext ξ
      exact ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)
    rw [← hset]
    exact mul_meas_ge_le_lintegral₀ hmeas2.aemeasurable _
  have hL : circleLevel n = (1 / 4 : ℝ) ^ n * (1 / 4 : ℝ) ^ n := by
    unfold circleLevel
    rw [← mul_pow]
    norm_num
  have ha0 : (0 : ℝ) < (1 / 4 : ℝ) ^ n := by positivity
  have hA : P {ξ | (1 / 4 : ℝ) ^ n ≤ Y ξ ^ 2} * ENNReal.ofReal ((1 / 4 : ℝ) ^ n) ≤
      ENNReal.ofReal ((1 / 4 : ℝ) ^ n) * ENNReal.ofReal ((1 / 4 : ℝ) ^ n) := by
    calc P {ξ | (1 / 4 : ℝ) ^ n ≤ Y ξ ^ 2} * ENNReal.ofReal ((1 / 4 : ℝ) ^ n)
        = ENNReal.ofReal ((1 / 4 : ℝ) ^ n) * P {ξ | (1 / 4 : ℝ) ^ n ≤ Y ξ ^ 2} := mul_comm _ _
      _ ≤ ∫⁻ ξ, ENNReal.ofReal (Y ξ ^ 2) ∂P := hmark
      _ = ENNReal.ofReal (∫ ξ, Y ξ ^ 2 ∂P) := (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
      _ ≤ ENNReal.ofReal ((1 / 4 : ℝ) ^ n * (1 / 4 : ℝ) ^ n) := ENNReal.ofReal_le_ofReal (hbound.trans_eq hL)
      _ = ENNReal.ofReal ((1 / 4 : ℝ) ^ n) * ENNReal.ofReal ((1 / 4 : ℝ) ^ n) :=
        ENNReal.ofReal_mul ha0.le
  have h0 : ENNReal.ofReal ((1 / 4 : ℝ) ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 ha0).ne'
  exact (ENNReal.mul_le_mul_iff_left h0 ENNReal.ofReal_ne_top).1 hA

/-- The first Borel-Cantelli lemma for one sequence with the `2^(-4n)` bound: the events `{(1/4)^n ≤ g_n²}` have
`P`-null `limsup`, because `∑ (1/4)^n < ∞`. -/
lemma measure_limsup_sq_eq_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (g : ℕ → Ω → ℝ)
    (hmeas : ∀ n, Measurable (g n)) (hint : ∀ n, Integrable (fun ξ => g n ξ ^ 2) P)
    (hbound : ∀ n, ∫ ξ, g n ξ ^ 2 ∂P ≤ circleLevel n) :
    P (Filter.limsup (fun n => {ξ | (1 / 4 : ℝ) ^ n ≤ g n ξ ^ 2}) atTop) = 0 := by
  refine measure_limsup_atTop_eq_zero ?_
  refine ne_top_of_le_ne_top (b := ∑' n : ℕ, ENNReal.ofReal ((1 / 4 : ℝ) ^ n)) ?_
    (ENNReal.tsum_le_tsum fun n => measure_sq_ge_le_ofReal (hmeas n) (hint n) (hbound n))
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
  exact ENNReal.ofReal_ne_top

/-- A countable union over the circles of the `limsup` events is measurable and `P`-null. -/
lemma measure_iUnion_limsup_sq {I : Type*} [Countable I] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (g : I → ℕ → Ω → ℝ) (hmeas : ∀ i n, Measurable (g i n))
    (hint : ∀ i n, Integrable (fun ξ => g i n ξ ^ 2) P)
    (hbound : ∀ i n, ∫ ξ, g i n ξ ^ 2 ∂P ≤ circleLevel n) :
    MeasurableSet (⋃ i, Filter.limsup (fun n => {ξ | (1 / 4 : ℝ) ^ n ≤ g i n ξ ^ 2}) atTop) ∧
      P (⋃ i, Filter.limsup (fun n => {ξ | (1 / 4 : ℝ) ^ n ≤ g i n ξ ^ 2}) atTop) = 0 :=
  ⟨MeasurableSet.iUnion fun i => MeasurableSet.measurableSet_limsup fun n =>
      measurableSet_le measurable_const ((hmeas i n).pow_const 2),
    measure_iUnion_null_iff.2 fun i => measure_limsup_sq_eq_zero (g i) (hmeas i) (hint i) (hbound i)⟩

/-- If `ξ` lies in only finitely many of the events `{(1/4)^n ≤ g_n(ξ)²}`, then `g_n(ξ) → 0`. -/
lemma tendsto_zero_of_not_mem_limsup {Ω : Type*} (g : ℕ → Ω → ℝ) {ξ : Ω}
    (hξ : ξ ∉ Filter.limsup (fun n => {ω | (1 / 4 : ℝ) ^ n ≤ g n ω ^ 2}) atTop) :
    Tendsto (fun n => g n ξ) atTop (𝓝 0) := by
  have hev : ∀ᶠ n in atTop, ξ ∉ {ω | (1 / 4 : ℝ) ^ n ≤ g n ω ^ 2} := by
    have h := hξ
    rw [mem_limsup_iff_frequently_mem, not_frequently] at h
    exact h
  have hsq : ∀ᶠ n in atTop, ‖g n ξ‖ ≤ (1 / 2 : ℝ) ^ n := by
    filter_upwards [hev] with n hn
    have hn' : ¬ ((1 / 4 : ℝ) ^ n ≤ g n ξ ^ 2) := hn
    have h1 : g n ξ ^ 2 < (1 / 4 : ℝ) ^ n := not_le.1 hn'
    have h2 : (1 / 4 : ℝ) ^ n = ((1 / 2 : ℝ) ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h2] at h1
    rw [Real.norm_eq_abs]
    exact (abs_lt_of_sq_lt_sq h1 (by positivity)).le
  exact squeeze_zero_norm' hsq (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

/-- The centred mollified circle pairing `⟨h, φ_e^{(w,r)}⟩ - h_r(w)` of a realization `ξ`. -/
noncomputable def circleDev {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (rho : ℂ → ℝ)
    (r : ℝ) (w : ℂ) (e : ℝ) (ξ : Ω) : ℝ :=
  hC ξ (circleMollifier rho w r e) - hcirc ξ r w

lemma measurable_circleDev {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho)
    {r : ℝ} (hr : 0 < r) (w : ℂ) {e : ℝ} (he : 0 < e) :
    Measurable (circleDev hC hcirc rho r w e) :=
  (hGFF.measurable_pairing _ (isTestFunction_circleMollifier (w := w) hρ hr he)).sub
    (hGFF.measurable_circle r w hr)

/-- The `L²` bound at the scales: `∫ (⟨h, φ_{ε_{i,n}}⟩ - h_{r_i}(w_i))² dP ≤ 2^(-4n)` for every whole-plane GFF. -/
lemma integral_sq_countableCircleScale_le {I : Type*} {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho)
    (q : I → CircleDomain) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) (i : I) (n : ℕ) :
    ∫ ξ, (hC ξ (circleMollifier rho (q i).val.2 (q i).val.1 (countableCircleScale hρ q i n))
      - hcirc ξ (q i).val.1 (q i).val.2) ^ 2 ∂P ≤ circleLevel n := by
  have hpos := countableCircleScale_pos hρ q i n
  have h := integral_sq_circleMollifier_sub_eq hGFF hρ (q i).property (q i).val.2 hpos
  have hlt := (circleThreshold_spec hρ q i n).2.2 _ hpos (countableCircleScale_lt_threshold hρ q i n)
  exact h.trans_le hlt.le

/-- **Countable mollified circle pairings converge almost surely.** For a literal mollifier `ρ` and a countable family
`q` of coded circles, with the deterministic scales `countableCircleScale hρ q` (fixed before any probability space):
for every whole-plane GFF `(P, hC, hcirc)`, the squared `L²(P)` errors are at most `2^(-4n)`, and there is a measurable
event `S` with `P Sᶜ = 0` on which `⟨h, φ_{ε_{i,n}}⟩ → h_{r_i}(w_i)` as `n → ∞`, for every `i`. -/
theorem countableCircleScale_ae_convergence {I : Type*} [Countable I] {rho : ℂ → ℝ}
    (hρ : IsLiteralMollifier rho) (q : I → CircleDomain) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) :
    (∀ (i : I) (n : ℕ), ∫ ξ, (hC ξ (circleMollifier rho (q i).val.2 (q i).val.1 (countableCircleScale hρ q i n))
      - hcirc ξ (q i).val.1 (q i).val.2) ^ 2 ∂P ≤ (2 : ℝ) ^ (-(4 * (n : ℤ)))) ∧
    ∃ S : Set Ω, MeasurableSet S ∧ P Sᶜ = 0 ∧ ∀ ξ ∈ S, ∀ i : I,
      Tendsto (fun n : ℕ => hC ξ (circleMollifier rho (q i).val.2 (q i).val.1 (countableCircleScale hρ q i n)))
        atTop (𝓝 (hcirc ξ (q i).val.1 (q i).val.2)) := by
  obtain ⟨hmeasU, hnullU⟩ := measure_iUnion_limsup_sq
    (fun i n ω => circleDev hC hcirc rho (q i).val.1 (q i).val.2 (countableCircleScale hρ q i n) ω)
    (fun i n => measurable_circleDev hGFF hρ (q i).property (q i).val.2 (countableCircleScale_pos hρ q i n))
    (fun i n => ((isWholePlaneGFF_circleMollifier_L2 hGFF hρ (q i).property (q i).val.2).1 _
      (countableCircleScale_pos hρ q i n)).integrable_sq)
    (fun i n => integral_sq_countableCircleScale_le hρ q hGFF i n)
  refine ⟨fun i n => ?_, _, hmeasU.compl, ?_, ?_⟩
  · rw [two_zpow_neg_four_mul]
    exact integral_sq_countableCircleScale_le hρ q hGFF i n
  · rw [compl_compl]
    exact hnullU
  · intro ξ hξ i
    have hξi : ξ ∉ Filter.limsup (fun n => {ω | (1 / 4 : ℝ) ^ n ≤
        (circleDev hC hcirc rho (q i).val.1 (q i).val.2 (countableCircleScale hρ q i n) ω) ^ 2}) atTop :=
      fun h => hξ (mem_iUnion.2 ⟨i, h⟩)
    exact tendsto_sub_nhds_zero_iff.1 (tendsto_zero_of_not_mem_limsup
      (fun n ω => circleDev hC hcirc rho (q i).val.1 (q i).val.2 (countableCircleScale hρ q i n) ω) hξi)

end HarmonicBalls
