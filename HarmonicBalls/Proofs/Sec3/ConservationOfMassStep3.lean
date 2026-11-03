import HarmonicBalls.Proofs.Sec3.PositiveDistribution
import HarmonicBalls.Steps.SecA.ObstacleConservationOfMass

/-!
# Lemma A.5: Step 3 (eq:weak-integration-by-parts, lines 3804-3827)

`obstacleConservationOfMassStep3_holds`: if `Δv = σ - t δ_z` on `B_R`, `v ≥ 0` on `B_R \ {z}`, `v` is continuous
on `closedBall 0 R \ {z}` and `v = 0` on `∂B_R`, then `σ(B_R) ≤ t`, with equality if `v` vanishes off a compact
subset of `B_R`.

Route (no weak normal derivative): radial test functions `φ(x) = F(|x|²)`, with `Δφ(x) = 4 (F'(s) + s F''(s))` at
`s = |x|²` (`laplacian_comp_norm_sq`). The profile `F = 1 - (∫_a^s m)/(∫_a^b m)` (`radialProfile`) has density
`m = T((s-a)/(a'-a)) (1 - T((s-c)/(b-c)))` (`T` the smooth transition), so that `Δφ = -(4/I) (m + s m') ≤ 0` for
`s < c` and `|Δφ| ≤ (4/I)(1 + b C/(b-c))` on the thin annulus `c ≤ |x|² ≤ b` near `∂B_R`, where `v` is small. Since
`v ≥ 0`, `∫ v Δφ ≤ sup_{annulus} v · (4π/I)(b - c + b C)`, which tends to `0`; with `φ = 1` on a compact `L ∋ z`,
`σ(L) ≤ ∫ φ dσ = t + ∫ v Δφ`. Equality case: a cut-off `χ = 1` near `K ∪ {z}` has `v Δχ = 0`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian
open scoped ContDiff ENNReal

/-! ## The Laplacian of a radial function -/

/-- The second derivative of `f` in the direction `v` is the second derivative of `t ↦ f(x + t v)` at `0`. -/
theorem iteratedFDeriv_two_apply_eq_iteratedDeriv {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (x v : ℂ) :
    iteratedFDeriv ℝ 2 f x ![v, v] = iteratedDeriv 2 (fun t : ℝ => f (x + t • v)) 0 := by
  let L : ℝ →L[ℝ] ℂ := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  have hL : ∀ t : ℝ, L t = t • v := fun t => by simp [L]
  have hg : (fun t : ℝ => f (x + t • v)) = (fun y => f (x + y)) ∘ L := by
    funext t
    simp only [Function.comp, hL]
  have hfx : ContDiff ℝ ∞ (fun y => f (x + y)) := hf.comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_eq_iteratedFDeriv, hg,
    ContinuousLinearMap.iteratedFDeriv_comp_right L hfx 0 (by norm_num),
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_left]
  simp only [hL, zero_smul, add_zero, one_smul]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem iteratedDeriv_two_comp_norm_sq_line {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (x v : ℂ) :
    iteratedDeriv 2 (fun t : ℝ => F (‖x + t • v‖ ^ 2)) 0 =
      deriv (deriv F) (‖x‖ ^ 2) * (2 * inner ℝ x v) ^ 2 + deriv F (‖x‖ ^ 2) * (2 * ‖v‖ ^ 2) := by
  obtain ⟨hF1, hF'⟩ := contDiff_infty_iff_deriv.1 hF
  have hF2 : Differentiable ℝ (deriv F) := (contDiff_infty_iff_deriv.1 hF').1
  set α := ‖x‖ ^ 2 with hα
  set β := 2 * inner ℝ x v with hβ
  set γ := ‖v‖ ^ 2 with hγ
  have hP : ∀ t : ℝ, ‖x + t • v‖ ^ 2 = α + β * t + γ * t ^ 2 := by
    intro t
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have hg : (fun t : ℝ => F (‖x + t • v‖ ^ 2)) = fun t => F (α + β * t + γ * t ^ 2) :=
    funext fun t => by rw [hP]
  have hPd : ∀ t : ℝ, HasDerivAt (fun t => α + β * t + γ * t ^ 2) (β + 2 * γ * t) t := by
    intro t
    have := (((hasDerivAt_id' t).const_mul β).const_add α).add ((hasDerivAt_pow 2 t).const_mul γ)
    exact this.congr_deriv (by norm_num; ring)
  have hd1 : deriv (fun t => F (α + β * t + γ * t ^ 2)) =
      fun t => deriv F (α + β * t + γ * t ^ 2) * (β + 2 * γ * t) := by
    funext t
    exact ((hF1 _).hasDerivAt.comp t (hPd t)).deriv
  have hlin : HasDerivAt (fun t : ℝ => β + 2 * γ * t) (2 * γ) 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).const_mul (2 * γ)).const_add β
    exact this.congr_deriv (by ring)
  have hd2 : HasDerivAt (fun t => deriv F (α + β * t + γ * t ^ 2) * (β + 2 * γ * t))
      (deriv (deriv F) (α + β * 0 + γ * 0 ^ 2) * (β + 2 * γ * 0) * (β + 2 * γ * 0) +
        deriv F (α + β * 0 + γ * 0 ^ 2) * (2 * γ)) 0 :=
    ((hF2 _).hasDerivAt.comp 0 (hPd 0)).mul hlin
  rw [hg, iteratedDeriv_succ, iteratedDeriv_one, hd1, hd2.deriv]
  norm_num
  ring

/-- **Laplacian of a radial function**: `Δ (F ∘ |·|²)(x) = 4 (F'(|x|²) + |x|² F''(|x|²))`. -/
theorem laplacian_comp_norm_sq {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (x : ℂ) :
    Δ (fun y : ℂ => F (‖y‖ ^ 2)) x = 4 * (deriv F (‖x‖ ^ 2) + ‖x‖ ^ 2 * deriv (deriv F) (‖x‖ ^ 2)) := by
  have hf : ContDiff ℝ ∞ (fun y : ℂ => F (‖y‖ ^ 2)) := hF.comp (contDiff_norm_sq ℝ)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  beta_reduce
  rw [iteratedFDeriv_two_apply_eq_iteratedDeriv hf, iteratedFDeriv_two_apply_eq_iteratedDeriv hf,
    iteratedDeriv_two_comp_norm_sq_line hF, iteratedDeriv_two_comp_norm_sq_line hF]
  have h1 : inner ℝ x (1 : ℂ) = x.re := by simp [Complex.inner]
  have h2 : inner ℝ x Complex.I = x.im := by simp [Complex.inner]
  have hn : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [h1, h2, norm_one, Complex.norm_I]
  have e : ∀ A B : ℝ, A * (2 * x.re) ^ 2 + B * (2 * 1 ^ 2) + (A * (2 * x.im) ^ 2 + B * (2 * 1 ^ 2)) =
      4 * (B + (x.re ^ 2 + x.im ^ 2) * A) := fun A B => by ring
  rw [e, ← hn]

/-! ## The radial profile -/

section Profile

variable {a a' c b : ℝ}

/-- The density `m(s) = T((s-a)/(a'-a)) (1 - T((s-c)/(b-c)))` of the radial profile (`T` the smooth transition):
`0` for `s ≤ a` and `s ≥ b`, `1` on `[a', c]`. -/
noncomputable def radialDensity (a a' c b s : ℝ) : ℝ :=
  Real.smoothTransition ((s - a) / (a' - a)) * (1 - Real.smoothTransition ((s - c) / (b - c)))

theorem contDiff_radialDensity (a a' c b : ℝ) : ContDiff ℝ ∞ (radialDensity a a' c b) := by
  unfold radialDensity
  have h1 : ContDiff ℝ ∞ fun s : ℝ => Real.smoothTransition ((s - a) / (a' - a)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  have h2 : ContDiff ℝ ∞ fun s : ℝ => Real.smoothTransition ((s - c) / (b - c)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  exact h1.mul (contDiff_const.sub h2)

theorem radialDensity_nonneg (s : ℝ) : 0 ≤ radialDensity a a' c b s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.2 (Real.smoothTransition.le_one _))

theorem radialDensity_le_one (s : ℝ) : radialDensity a a' c b s ≤ 1 := by
  have h1 := Real.smoothTransition.le_one ((s - a) / (a' - a))
  have h2 := Real.smoothTransition.nonneg ((s - a) / (a' - a))
  have h3 := Real.smoothTransition.le_one ((s - c) / (b - c))
  have h4 := Real.smoothTransition.nonneg ((s - c) / (b - c))
  rw [radialDensity]
  nlinarith

theorem radialDensity_eq_zero_of_le (ha : a < a') {s : ℝ} (hs : s ≤ a) : radialDensity a a' c b s = 0 := by
  rw [radialDensity, Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)), zero_mul]

theorem radialDensity_eq_zero_of_ge (hb : c < b) {s : ℝ} (hs : b ≤ s) : radialDensity a a' c b s = 0 := by
  rw [radialDensity, Real.smoothTransition.one_of_one_le (x := (s - c) / (b - c))
    ((one_le_div (by linarith)).2 (by linarith)), sub_self, mul_zero]

theorem radialDensity_eq_one (ha : a < a') (hb : c < b) {s : ℝ} (h1 : a' ≤ s) (h2 : s ≤ c) :
    radialDensity a a' c b s = 1 := by
  rw [radialDensity, Real.smoothTransition.one_of_one_le (x := (s - a) / (a' - a))
    ((one_le_div (by linarith)).2 (by linarith)), Real.smoothTransition.zero_of_nonpos (x := (s - c) / (b - c))
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)), sub_zero, one_mul]

theorem deriv_radialDensity_eq_zero_of_lt (ha : a < a') {s : ℝ} (hs : s < a) :
    deriv (radialDensity a a' c b) s = 0 := by
  have heq : radialDensity a a' c b =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hs] with u hu
    exact radialDensity_eq_zero_of_le ha (le_of_lt hu)
  rw [heq.deriv_eq, deriv_const]

theorem deriv_radialDensity_eq_zero_of_gt (hb : c < b) {s : ℝ} (hs : b < s) :
    deriv (radialDensity a a' c b) s = 0 := by
  have heq : radialDensity a a' c b =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hs] with u hu
    exact radialDensity_eq_zero_of_ge hb (le_of_lt hu)
  rw [heq.deriv_eq, deriv_const]

theorem deriv_radialDensity_nonneg (ha : a < a') (hb : c < b) {s : ℝ} (hs : s < c) :
    0 ≤ deriv (radialDensity a a' c b) s := by
  have heq : radialDensity a a' c b =ᶠ[𝓝 s] fun u => Real.smoothTransition ((u - a) / (a' - a)) := by
    filter_upwards [Iio_mem_nhds hs] with u hu
    rw [radialDensity, Real.smoothTransition.zero_of_nonpos (x := (u - c) / (b - c))
      (div_nonpos_of_nonpos_of_nonneg (by linarith [mem_Iio.1 hu]) (by linarith)), sub_zero, mul_one]
  rw [heq.deriv_eq]
  exact (Real.smoothTransition.monotone.comp fun u w huw =>
    div_le_div_of_nonneg_right (by linarith) (by linarith)).deriv_nonneg

theorem exists_bound_deriv_smoothTransition : ∃ C, 0 ≤ C ∧ ∀ y, |deriv Real.smoothTransition y| ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hcs : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun y hy => ?_
    simp only [mem_Icc, not_and_or, not_le] at hy
    rcases hy with hy | hy
    · have heq : Real.smoothTransition =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds hy] with u hu
        exact Real.smoothTransition.zero_of_nonpos (le_of_lt hu)
      rw [heq.deriv_eq, deriv_const]
    · have heq : Real.smoothTransition =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hy] with u hu
        exact Real.smoothTransition.one_of_one_le (le_of_lt hu)
      rw [heq.deriv_eq, deriv_const]
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  exact ⟨C, (norm_nonneg _).trans (hC 0), fun y => by rw [← Real.norm_eq_abs]; exact hC y⟩

theorem abs_deriv_radialDensity_le (ha : a < a') (hb : c < b) {C : ℝ}
    (hC : ∀ y, |deriv Real.smoothTransition y| ≤ C) {s : ℝ} (hs : a' < s) :
    |deriv (radialDensity a a' c b) s| ≤ C / (b - c) := by
  have heq : radialDensity a a' c b =ᶠ[𝓝 s] fun u => 1 - Real.smoothTransition ((u - c) / (b - c)) := by
    filter_upwards [Ioi_mem_nhds hs] with u hu
    rw [radialDensity, Real.smoothTransition.one_of_one_le (x := (u - a) / (a' - a))
      ((one_le_div (by linarith)).2 (by linarith [mem_Ioi.1 hu])), one_mul]
  have hd : HasDerivAt (fun u => 1 - Real.smoothTransition ((u - c) / (b - c)))
      (-(deriv Real.smoothTransition ((s - c) / (b - c)) * (1 / (b - c)))) s := by
    have h1 : HasDerivAt (fun u => (u - c) / (b - c)) (1 / (b - c)) s :=
      ((hasDerivAt_id' s).sub_const c).div_const (b - c)
    have h2 := ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) _).hasDerivAt.comp s h1
    exact h2.const_sub 1
  have hbc : 0 < 1 / (b - c) := one_div_pos.2 (by linarith)
  rw [heq.deriv_eq, hd.deriv, abs_neg, abs_mul, abs_of_pos hbc, div_eq_mul_one_div C]
  exact mul_le_mul_of_nonneg_right (hC _) hbc.le

/-- The radial profile `F(s) = 1 - (∫_a^s m) / (∫_a^b m)`: `1` for `s ≤ a`, `0` for `s ≥ b`, nonincreasing. -/
noncomputable def radialProfile (a a' c b s : ℝ) : ℝ :=
  1 - (∫ u in a..s, radialDensity a a' c b u) / ∫ u in a..b, radialDensity a a' c b u

theorem intervalIntegrable_radialDensity (p q : ℝ) :
    IntervalIntegrable (radialDensity a a' c b) volume p q :=
  (contDiff_radialDensity a a' c b).continuous.intervalIntegrable p q

theorem integral_radialDensity_ge (ha : a < a') (hc : a' < c) (hb : c < b) :
    c - a' ≤ ∫ u in a..b, radialDensity a a' c b u := by
  have hi := intervalIntegrable_radialDensity (a := a) (a' := a') (c := c) (b := b)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi a a') (hi a' b),
    ← intervalIntegral.integral_add_adjacent_intervals (hi a' c) (hi c b)]
  have heq : EqOn (radialDensity a a' c b) (fun _ => (1 : ℝ)) (uIcc a' c) := fun u hu => by
    rw [uIcc_of_le hc.le] at hu
    exact radialDensity_eq_one ha hb hu.1 hu.2
  have h1 : ∫ u in a'..c, radialDensity a a' c b u = c - a' := by
    rw [intervalIntegral.integral_congr heq]
    simp
  have h0 : 0 ≤ ∫ u in a..a', radialDensity a a' c b u :=
    intervalIntegral.integral_nonneg ha.le fun u _ => radialDensity_nonneg u
  have h2 : 0 ≤ ∫ u in c..b, radialDensity a a' c b u :=
    intervalIntegral.integral_nonneg hb.le fun u _ => radialDensity_nonneg u
  linarith

theorem radialProfile_eq_one (ha : a < a') {s : ℝ} (hs : s ≤ a) : radialProfile a a' c b s = 1 := by
  have heq : EqOn (radialDensity a a' c b) (fun _ => (0 : ℝ)) (uIcc s a) := fun u hu => by
    rw [uIcc_of_le hs] at hu
    exact radialDensity_eq_zero_of_le ha hu.2
  have h0 : ∫ u in a..s, radialDensity a a' c b u = 0 := by
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_congr heq]
    simp
  rw [radialProfile, h0, zero_div, sub_zero]

theorem radialProfile_eq_zero (ha : a < a') (hc : a' < c) (hb : c < b) {s : ℝ} (hs : b ≤ s) :
    radialProfile a a' c b s = 0 := by
  have hI : 0 < ∫ u in a..b, radialDensity a a' c b u := by linarith [integral_radialDensity_ge ha hc hb]
  have hi := intervalIntegrable_radialDensity (a := a) (a' := a') (c := c) (b := b)
  have heq : EqOn (radialDensity a a' c b) (fun _ => (0 : ℝ)) (uIcc b s) := fun u hu => by
    rw [uIcc_of_le hs] at hu
    exact radialDensity_eq_zero_of_ge hb hu.1
  have h0 : ∫ u in a..s, radialDensity a a' c b u = ∫ u in a..b, radialDensity a a' c b u := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi a b) (hi b s), intervalIntegral.integral_congr heq]
    simp
  rw [radialProfile, h0, div_self hI.ne', sub_self]

theorem radialProfile_nonneg (ha : a < a') (hc : a' < c) (hb : c < b) (s : ℝ) :
    0 ≤ radialProfile a a' c b s := by
  rcases le_or_gt s a with hs | hs
  · rw [radialProfile_eq_one ha hs]
    norm_num
  rcases le_or_gt b s with hs' | hs'
  · rw [radialProfile_eq_zero ha hc hb hs']
  have hI : 0 < ∫ u in a..b, radialDensity a a' c b u := by linarith [integral_radialDensity_ge ha hc hb]
  have hi := intervalIntegrable_radialDensity (a := a) (a' := a') (c := c) (b := b)
  have hle : ∫ u in a..s, radialDensity a a' c b u ≤ ∫ u in a..b, radialDensity a a' c b u := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi a s) (hi s b)]
    have : 0 ≤ ∫ u in s..b, radialDensity a a' c b u :=
      intervalIntegral.integral_nonneg hs'.le fun u _ => radialDensity_nonneg u
    linarith
  rw [radialProfile, sub_nonneg, div_le_one hI]
  exact hle

theorem hasDerivAt_radialProfile (s : ℝ) :
    HasDerivAt (radialProfile a a' c b)
      (-(radialDensity a a' c b s / ∫ u in a..b, radialDensity a a' c b u)) s := by
  have h := ((contDiff_radialDensity a a' c b).continuous.integral_hasStrictDerivAt a s).hasDerivAt
  exact (h.div_const (∫ u in a..b, radialDensity a a' c b u)).const_sub 1

theorem deriv_radialProfile : deriv (radialProfile a a' c b) =
    fun s => -(radialDensity a a' c b s / ∫ u in a..b, radialDensity a a' c b u) :=
  funext fun s => (hasDerivAt_radialProfile s).deriv

theorem contDiff_radialProfile : ContDiff ℝ ∞ (radialProfile a a' c b) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun s => (hasDerivAt_radialProfile s).differentiableAt, ?_⟩
  rw [deriv_radialProfile]
  exact ((contDiff_radialDensity a a' c b).div_const _).neg

theorem deriv_deriv_radialProfile (s : ℝ) :
    deriv (deriv (radialProfile a a' c b)) s =
      -(deriv (radialDensity a a' c b) s / ∫ u in a..b, radialDensity a a' c b u) := by
  rw [deriv_radialProfile]
  have hd := ((contDiff_radialDensity a a' c b).differentiable (by simp) s).hasDerivAt
  exact ((hd.div_const (∫ u in a..b, radialDensity a a' c b u)).neg).deriv

/-- `Δ φ = -(4/I) (m(s) + s m'(s))` at `s = |x|²`, for `φ(x) = F(|x|²)` and `I = ∫_a^b m`. -/
theorem laplacian_radialProfile (x : ℂ) :
    Δ (fun y : ℂ => radialProfile a a' c b (‖y‖ ^ 2)) x =
      -(4 / ∫ u in a..b, radialDensity a a' c b u) *
        (radialDensity a a' c b (‖x‖ ^ 2) + ‖x‖ ^ 2 * deriv (radialDensity a a' c b) (‖x‖ ^ 2)) := by
  rw [laplacian_comp_norm_sq contDiff_radialProfile, deriv_deriv_radialProfile, deriv_radialProfile]
  ring

end Profile

/-! ## Step 3 -/

/-- `σ(K) ≤ ∫ φ dσ` for an integrable `φ ≥ 0` with `φ ≥ 1` on `K`. -/
theorem measure_le_ofReal_integral {σ : Measure ℂ} {K : Set ℂ} (hK : MeasurableSet K) {φ : ℂ → ℝ}
    (hφi : Integrable φ σ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x ∈ K, 1 ≤ φ x) :
    σ K ≤ ENNReal.ofReal (∫ x, φ x ∂σ) := by
  rw [ofReal_integral_eq_lintegral_ofReal hφi (Eventually.of_forall hφ0), ← lintegral_indicator_one hK]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ K
  · simp only [indicator_of_mem hx, Pi.one_apply]
    exact ENNReal.one_le_ofReal.2 (hφ1 x hx)
  · simp [hx]

/-- **Lemma A.5, Step 3** (`ObstacleConservationOfMassStep3`). -/
theorem obstacleConservationOfMassStep3_holds : ObstacleConservationOfMassStep3 := by
  intro R z t σ v hR hz ht hΔ hv0 hvc hvS
  have hid : ∀ φ, IsTestFunction (ball (0 : ℂ) R) φ → ∫ x, φ x ∂σ = (∫ x, v x * Δ φ x) + t * φ z := by
    intro φ hφ
    obtain ⟨-, -, h⟩ := hΔ.2 φ hφ
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal ht, smul_eq_mul] at h
    linarith
  have hle : σ (ball 0 R) ≤ ENNReal.ofReal t := by
    apply measure_isOpen_le_of_forall_isCompact isOpen_ball
    intro L hL hLB
    obtain ⟨ρ₁, hρ₁R, hLρ⟩ := exists_lt_subset_ball (hL.isClosed.union isClosed_singleton)
      (union_subset hLB (singleton_subset_iff.2 hz))
    have hzρ : ‖z‖ < ρ₁ := mem_ball_zero_iff.1 (hLρ (Or.inr rfl))
    have hρ₁ : 0 < ρ₁ := (norm_nonneg z).trans_lt hzρ
    obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_smoothTransition
    obtain ⟨ρ₂, hρ₂⟩ : ∃ r : ℝ, r = (ρ₁ + R) / 2 := ⟨_, rfl⟩
    obtain ⟨ρ₃, hρ₃⟩ : ∃ r : ℝ, r = (ρ₂ + R) / 2 := ⟨_, rfl⟩
    have h12 : ρ₁ < ρ₂ := by rw [hρ₂]; linarith
    have h23 : ρ₂ < ρ₃ := by rw [hρ₃]; linarith
    have h3R : ρ₃ < R := by rw [hρ₃]; linarith
    have hρ₂0 : 0 < ρ₂ := by linarith
    obtain ⟨D, hD⟩ : ∃ d : ℝ, d = ρ₃ ^ 2 - ρ₂ ^ 2 := ⟨_, rfl⟩
    have hDpos : 0 < D := by rw [hD]; exact sub_pos.2 (pow_lt_pow_left₀ h23 hρ₂0.le two_ne_zero)
    suffices h : ∀ ε > 0, σ L ≤ ENNReal.ofReal (t + ε) by
      refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      have := h ε (NNReal.coe_pos.2 hε)
      rwa [ENNReal.ofReal_add ht ε.coe_nonneg, ENNReal.ofReal_coe_nnreal] at this
    intro ε hε
    have hRC : 0 ≤ R ^ 2 + R ^ 2 * C := add_nonneg (sq_nonneg R) (mul_nonneg (sq_nonneg R) hC0)
    have hπ : (0 : ℝ) ≤ 4 * Real.pi := by positivity
    obtain ⟨K₀, hK₀⟩ : ∃ k : ℝ, k = 4 * Real.pi * (R ^ 2 + R ^ 2 * C) / D + 1 := ⟨_, rfl⟩
    have hK₀1 : 1 ≤ K₀ := by
      have := div_nonneg (mul_nonneg hπ hRC) hDpos.le
      rw [hK₀]; linarith
    have hK₀pos : 0 < K₀ := by linarith
    obtain ⟨η, hη⟩ : ∃ e : ℝ, e = ε / K₀ := ⟨_, rfl⟩
    have hηpos : 0 < η := by rw [hη]; exact div_pos hε hK₀pos
    have hηK : η * K₀ = ε := by
      have hK₀0 : K₀ ≠ 0 := hK₀pos.ne'
      rw [hη]; field_simp
    -- `v` is small near the boundary circle
    have hAnnc : IsCompact (closedBall (0 : ℂ) R \ ball 0 ρ₁) := (isCompact_closedBall 0 R).diff isOpen_ball
    have hAnnz : closedBall (0 : ℂ) R \ ball 0 ρ₁ ⊆ closedBall 0 R \ {z} := fun x hx =>
      ⟨hx.1, fun h => hx.2 (by rw [h]; exact mem_ball_zero_iff.2 hzρ)⟩
    obtain ⟨δ', hδ', hδ'v⟩ := Metric.uniformContinuousOn_iff.1
      (hAnnc.uniformContinuousOn_of_continuous (hvc.mono hAnnz)) η hηpos
    obtain ⟨rc, hrc⟩ : ∃ r : ℝ, r = max ρ₃ (R - δ' / 2) := ⟨_, rfl⟩
    obtain ⟨rb, hrb⟩ : ∃ r : ℝ, r = (rc + R) / 2 := ⟨_, rfl⟩
    have hρ₃rc : ρ₃ ≤ rc := by rw [hrc]; exact le_max_left _ _
    have hrcδ : R - δ' / 2 ≤ rc := by rw [hrc]; exact le_max_right _ _
    have hrcR : rc < R := by rw [hrc]; exact max_lt h3R (by linarith)
    have hrcrb : rc < rb := by rw [hrb]; linarith
    have hrbR : rb < R := by rw [hrb]; linarith
    have hrc0 : 0 < rc := by linarith
    have hvsmall : ∀ x : ℂ, rc ≤ ‖x‖ → ‖x‖ ≤ rb → v x < η := by
      intro x hx1 hx2
      have hxpos : 0 < ‖x‖ := by linarith
      have hxAnn : x ∈ closedBall (0 : ℂ) R \ ball 0 ρ₁ := ⟨mem_closedBall_zero_iff.2 (by linarith), fun h => by
        have := mem_ball_zero_iff.1 h
        linarith⟩
      have hyn : ‖(R / ‖x‖) • x‖ = R := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR hxpos), div_mul_cancel₀ R hxpos.ne']
      have hyAnn : (R / ‖x‖) • x ∈ closedBall (0 : ℂ) R \ ball 0 ρ₁ :=
        ⟨mem_closedBall_zero_iff.2 hyn.le, fun h => by
          have := mem_ball_zero_iff.1 h
          linarith⟩
      have hxy : dist x ((R / ‖x‖) • x) = R - ‖x‖ := by
        have hge : 1 ≤ R / ‖x‖ := (one_le_div hxpos).2 (by linarith)
        rw [dist_eq_norm, show x - (R / ‖x‖) • x = (1 - R / ‖x‖) • x by rw [sub_smul, one_smul],
          norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith), neg_sub, sub_mul,
          div_mul_cancel₀ R hxpos.ne', one_mul]
      have := hδ'v x hxAnn _ hyAnn (by rw [hxy]; linarith)
      rw [hvS _ (mem_sphere_zero_iff_norm.2 hyn), Real.dist_eq, sub_zero] at this
      exact lt_of_abs_lt this
    -- the profile
    obtain ⟨a, ha_def⟩ : ∃ s : ℝ, s = ρ₁ ^ 2 := ⟨_, rfl⟩
    obtain ⟨a', ha'_def⟩ : ∃ s : ℝ, s = ρ₂ ^ 2 := ⟨_, rfl⟩
    obtain ⟨c, hc_def⟩ : ∃ s : ℝ, s = rc ^ 2 := ⟨_, rfl⟩
    obtain ⟨b, hb_def⟩ : ∃ s : ℝ, s = rb ^ 2 := ⟨_, rfl⟩
    have haa' : a < a' := by rw [ha_def, ha'_def]; exact pow_lt_pow_left₀ h12 hρ₁.le two_ne_zero
    have ha'c : a' < c := by
      rw [ha'_def, hc_def]; exact pow_lt_pow_left₀ (h23.trans_le hρ₃rc) hρ₂0.le two_ne_zero
    have hcb : c < b := by rw [hc_def, hb_def]; exact pow_lt_pow_left₀ hrcrb hrc0.le two_ne_zero
    have hbR : b ≤ R ^ 2 := by rw [hb_def]; exact pow_le_pow_left₀ (by linarith) hrbR.le 2
    have hc0 : 0 ≤ c := by rw [hc_def]; positivity
    obtain ⟨I, hI_def⟩ : ∃ i : ℝ, i = ∫ u in a..b, radialDensity a a' c b u := ⟨_, rfl⟩
    have hI : D ≤ I := by
      have h1 := integral_radialDensity_ge haa' ha'c hcb
      have h2 : ρ₃ ^ 2 ≤ rc ^ 2 := pow_le_pow_left₀ (by linarith) hρ₃rc 2
      have h3 : D ≤ c - a' := by rw [hD, hc_def, ha'_def]; linarith
      rw [hI_def]; linarith
    have hIpos : 0 < I := hDpos.trans_le hI
    obtain ⟨φ, hφ_def⟩ : ∃ f : ℂ → ℝ, f = fun x => radialProfile a a' c b (‖x‖ ^ 2) := ⟨_, rfl⟩
    have hφd : ContDiff ℝ ∞ φ := by rw [hφ_def]; exact contDiff_radialProfile.comp (contDiff_norm_sq ℝ)
    have hφsupp : Function.support φ ⊆ ball 0 rb := by
      intro x hx
      by_contra hxb
      apply hx
      have h1 : rb ≤ ‖x‖ := by simpa using hxb
      rw [hφ_def]
      exact radialProfile_eq_zero haa' ha'c hcb (by rw [hb_def]; exact pow_le_pow_left₀ (by linarith) h1 2)
    have hφts : tsupport φ ⊆ closedBall 0 rb :=
      closure_minimal (hφsupp.trans ball_subset_closedBall) isClosed_closedBall
    have hφT : IsTestFunction (ball (0 : ℂ) R) φ :=
      ⟨hφd, (isCompact_closedBall 0 rb).of_isClosed_subset (isClosed_tsupport _) hφts,
        hφts.trans (closedBall_subset_ball hrbR)⟩
    have hφ0 : ∀ x, 0 ≤ φ x := fun x => by rw [hφ_def]; exact radialProfile_nonneg haa' ha'c hcb _
    have hφ1 : ∀ x : ℂ, ‖x‖ < ρ₁ → φ x = 1 := fun x hx => by
      rw [hφ_def]
      exact radialProfile_eq_one haa' (by rw [ha_def]; exact pow_le_pow_left₀ (norm_nonneg x) hx.le 2)
    have hΔφ : ∀ x, Δ φ x = -(4 / I) *
        (radialDensity a a' c b (‖x‖ ^ 2) + ‖x‖ ^ 2 * deriv (radialDensity a a' c b) (‖x‖ ^ 2)) :=
      fun x => by rw [hφ_def, hI_def]; exact laplacian_radialProfile x
    -- the pointwise bound `v Δφ ≤ M 1_A`
    have hbc : 0 < b - c := by linarith
    have hb0 : 0 ≤ b := by linarith
    have hbC : 0 ≤ b * C / (b - c) := div_nonneg (mul_nonneg hb0 hC0) hbc.le
    have h4I : 0 < 4 / I := div_pos four_pos hIpos
    obtain ⟨M, hM⟩ : ∃ m : ℝ, m = η * (4 / I * (1 + b * C / (b - c))) := ⟨_, rfl⟩
    have hM0 : 0 ≤ M := by rw [hM]; exact mul_nonneg hηpos.le (mul_nonneg h4I.le (by linarith))
    obtain ⟨A, hA⟩ : ∃ S : Set ℂ, S = closedBall (0 : ℂ) rb \ ball 0 rc := ⟨_, rfl⟩
    have hAmeas : MeasurableSet A := by rw [hA]; exact measurableSet_closedBall.diff measurableSet_ball
    have hpt : ∀ x, v x * Δ φ x ≤ A.indicator (fun _ => M) x := by
      intro x
      have hind0 : 0 ≤ A.indicator (fun _ => M) x := indicator_nonneg (fun _ _ => hM0) x
      rw [hΔφ x]
      have hs0 : 0 ≤ ‖x‖ ^ 2 := by positivity
      by_cases hsa : ‖x‖ ^ 2 < a
      · rw [radialDensity_eq_zero_of_le haa' hsa.le, deriv_radialDensity_eq_zero_of_lt haa' hsa]
        simpa using hind0
      by_cases hsc : ‖x‖ ^ 2 < c
      · have hxz : x ≠ z := by
          rintro rfl
          apply hsa
          rw [ha_def]
          exact pow_lt_pow_left₀ hzρ (norm_nonneg _) two_ne_zero
        have hxR : ‖x‖ < R := by
          by_contra hxR
          rw [not_lt] at hxR
          have : R ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ hR.le hxR 2
          linarith
        have hvx := hv0 x (mem_ball_zero_iff.2 hxR) hxz
        have hm := radialDensity_nonneg (a := a) (a' := a') (c := c) (b := b) (‖x‖ ^ 2)
        have hm' := deriv_radialDensity_nonneg (c := c) (b := b) haa' hcb hsc
        have hE : 0 ≤ radialDensity a a' c b (‖x‖ ^ 2) +
            ‖x‖ ^ 2 * deriv (radialDensity a a' c b) (‖x‖ ^ 2) :=
          add_nonneg hm (mul_nonneg hs0 hm')
        have hneg := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 h4I.le) hE
        exact (mul_nonpos_of_nonneg_of_nonpos hvx hneg).trans hind0
      by_cases hsb : b < ‖x‖ ^ 2
      · rw [radialDensity_eq_zero_of_ge hcb hsb.le, deriv_radialDensity_eq_zero_of_gt hcb hsb]
        simpa using hind0
      rw [not_lt] at hsa hsc hsb
      have hxr1 : rc ≤ ‖x‖ :=
        (pow_le_pow_iff_left₀ hrc0.le (norm_nonneg x) two_ne_zero).1 (by rw [← hc_def]; exact hsc)
      have hxr2 : ‖x‖ ≤ rb :=
        (pow_le_pow_iff_left₀ (norm_nonneg x) (by linarith) two_ne_zero).1 (by rw [← hb_def]; exact hsb)
      have hxA : x ∈ A := by
        rw [hA]
        exact ⟨mem_closedBall_zero_iff.2 hxr2, fun h => by
          have := mem_ball_zero_iff.1 h
          linarith⟩
      rw [indicator_of_mem hxA]
      have hvx : v x < η := hvsmall x hxr1 hxr2
      have hxz : x ≠ z := by
        rintro rfl
        linarith
      have hvx0 : 0 ≤ v x := hv0 x (mem_ball_zero_iff.2 (by linarith)) hxz
      have hm := radialDensity_nonneg (a := a) (a' := a') (c := c) (b := b) (‖x‖ ^ 2)
      have hm1 := radialDensity_le_one (a := a) (a' := a') (c := c) (b := b) (‖x‖ ^ 2)
      have hm' := abs_deriv_radialDensity_le (a := a) (c := c) haa' hcb hC (s := ‖x‖ ^ 2) (by linarith)
      have hbound : |radialDensity a a' c b (‖x‖ ^ 2) + ‖x‖ ^ 2 * deriv (radialDensity a a' c b) (‖x‖ ^ 2)| ≤
          1 + b * C / (b - c) := by
        have h1 : |‖x‖ ^ 2 * deriv (radialDensity a a' c b) (‖x‖ ^ 2)| ≤ b * (C / (b - c)) := by
          rw [abs_mul, abs_of_nonneg hs0]
          exact mul_le_mul hsb hm' (abs_nonneg _) hb0
        have h2 := abs_add_le (radialDensity a a' c b (‖x‖ ^ 2))
          (‖x‖ ^ 2 * deriv (radialDensity a a' c b) (‖x‖ ^ 2))
        rw [abs_of_nonneg hm] at h2
        have h3 : b * (C / (b - c)) = b * C / (b - c) := by ring
        linarith
      generalize radialDensity a a' c b (‖x‖ ^ 2) + ‖x‖ ^ 2 * deriv (radialDensity a a' c b) (‖x‖ ^ 2) = E
        at hbound ⊢
      calc v x * (-(4 / I) * E) ≤ |v x * (-(4 / I) * E)| := le_abs_self _
        _ = v x * ((4 / I) * |E|) := by
          rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hvx0, abs_of_pos h4I]
        _ ≤ η * ((4 / I) * (1 + b * C / (b - c))) :=
          mul_le_mul hvx.le (mul_le_mul_of_nonneg_left hbound h4I.le)
            (mul_nonneg h4I.le (abs_nonneg _)) hηpos.le
        _ = M := hM.symm
    -- the volume of the annulus
    have hvolA : (volume A).toReal = Real.pi * (b - c) := by
      have hsub : ball (0 : ℂ) rc ⊆ closedBall 0 rb := ball_subset_closedBall.trans
        (closedBall_subset_closedBall hrcrb.le)
      rw [hA, measure_sdiff hsub measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne,
        Complex.volume_closedBall, Complex.volume_ball]
      have hle' : ENNReal.ofReal rc ^ 2 * (NNReal.pi : ℝ≥0∞) ≤ ENNReal.ofReal rb ^ 2 * (NNReal.pi : ℝ≥0∞) := by
        gcongr
      rw [ENNReal.toReal_sub_of_le hle' (by finiteness)]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hrc0.le,
        ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ rb), ENNReal.coe_toReal, NNReal.coe_real_pi]
      rw [hb_def, hc_def]
      ring
    have hint_le : ∫ x, v x * Δ φ x ≤ M * (Real.pi * (b - c)) := by
      have hAfin : volume A ≠ ⊤ := by
        rw [hA]
        exact ((measure_mono sdiff_subset).trans_lt measure_closedBall_lt_top).ne
      have hgi : Integrable (A.indicator fun _ => M) :=
        (integrableOn_const hAfin).integrable_indicator hAmeas
      calc ∫ x, v x * Δ φ x ≤ ∫ x, A.indicator (fun _ => M) x :=
            integral_mono (integrable_mul_laplacian hΔ.1 hφT) hgi hpt
        _ = (volume A).toReal * M := by rw [integral_indicator_const M hAmeas, smul_eq_mul, measureReal_def]
        _ = M * (Real.pi * (b - c)) := by rw [hvolA]; ring
    have hfinal : M * (Real.pi * (b - c)) ≤ η * (K₀ - 1) := by
      have hI0 : I ≠ 0 := hIpos.ne'
      have hbc0 : b - c ≠ 0 := hbc.ne'
      have e1 : M * (Real.pi * (b - c)) = η * (4 * Real.pi * ((b - c) + b * C) / I) := by
        rw [hM]
        field_simp
      have e2 : K₀ - 1 = 4 * Real.pi * (R ^ 2 + R ^ 2 * C) / D := by rw [hK₀]; ring
      rw [e1, e2]
      refine mul_le_mul_of_nonneg_left ?_ hηpos.le
      refine div_le_div₀ (mul_nonneg hπ hRC) ?_ hDpos hI
      have h1 : (b - c) + b * C ≤ R ^ 2 + R ^ 2 * C := by
        have : b * C ≤ R ^ 2 * C := mul_le_mul_of_nonneg_right hbR hC0
        linarith
      exact mul_le_mul_of_nonneg_left h1 hπ
    have hσL := measure_le_ofReal_integral hL.measurableSet (hΔ.2 φ hφT).1 hφ0
      (fun x hx => (hφ1 x (mem_ball_zero_iff.1 (hLρ (Or.inl hx)))).ge)
    rw [hid φ hφT, hφ1 z hzρ, mul_one] at hσL
    refine hσL.trans (ENNReal.ofReal_le_ofReal ?_)
    have : η * (K₀ - 1) = ε - η := by rw [mul_sub, hηK, mul_one]
    linarith [hint_le, hfinal]
  refine ⟨hle, ?_⟩
  rintro ⟨K, hK, hKB, hvK⟩
  refine le_antisymm hle ?_
  have hKz : IsCompact (K ∪ {z}) := hK.union isCompact_singleton
  obtain ⟨δ, hδ, hδB⟩ := hKz.exists_cthickening_subset_open isOpen_ball
    (union_subset hKB (singleton_subset_iff.2 hz))
  obtain ⟨χ, hχd, hχc, hχU, hχ01, hχ1⟩ :=
    exists_cutoff_of_isCompact_subset_isOpen hKz.cthickening isOpen_ball hδB
  have hχ : IsTestFunction (ball (0 : ℂ) R) χ := ⟨hχd, hχc, hχU⟩
  have hΔχ : ∀ x ∈ K ∪ {z}, Δ χ x = 0 := by
    intro x hx
    have heq : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [ball_mem_nhds x hδ] with y hy
      exact hχ1 y (mem_cthickening_of_dist_le y x δ _ hx (mem_ball.1 hy).le)
    rw [(InnerProductSpace.laplacian_congr_nhds heq).self_of_nhds]
    simp
  have hvχ : (fun x => v x * Δ χ x) = fun _ => 0 := by
    funext x
    by_cases hx : x ∈ K
    · rw [hΔχ x (Or.inl hx), mul_zero]
    by_cases hxB : x ∈ ball (0 : ℂ) R
    · rw [hvK x ⟨hxB, hx⟩, zero_mul]
    · rw [laplacian_eq_zero_of_notMem_tsupport (fun h => hxB (hχU h)), mul_zero]
  have hint := hid χ hχ
  rw [hvχ, integral_zero, zero_add, hχ1 z (self_subset_cthickening _ (Or.inr rfl)), mul_one] at hint
  calc ENNReal.ofReal t = ENNReal.ofReal (∫ x, χ x ∂σ) := by rw [hint]
    _ = ∫⁻ x, ENNReal.ofReal (χ x) ∂σ :=
        ofReal_integral_eq_lintegral_ofReal (hΔ.2 χ hχ).1 (Eventually.of_forall fun x => (hχ01 x).1)
    _ ≤ ∫⁻ x, (ball (0 : ℂ) R).indicator 1 x ∂σ := lintegral_mono fun x => by
        by_cases hx : x ∈ ball (0 : ℂ) R
        · simp only [indicator_of_mem hx, Pi.one_apply]
          exact ENNReal.ofReal_le_one.2 (hχ01 x).2
        · have : χ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hχU h)
          simp [hx, this]
    _ = σ (ball 0 R) := lintegral_indicator_one isOpen_ball.measurableSet

end HarmonicBalls
