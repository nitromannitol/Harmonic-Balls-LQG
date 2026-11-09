import HarmonicBalls.Defs.GFF
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Dilation of the whole-plane GFF: deterministic identities (Step 8 of the 11.13 proof, owner n3)

Source: corrected paper, lemma `s11-pinch:lem:mixing` (tex lines 3769-3812), the dilation `𝒯 g = g(·/2)`.
On pairings, `(𝒯ⁿ g, k) = (g, κₙ k)` with `κₙ k (y) = 4ⁿ k (2ⁿ • y)` (`dilateTest`). This file proves the
deterministic facts used for the covariance decay of the dilation (`Cov((g,f),(𝒯ⁿg,k)) → 0`):
test functions and integral zero are preserved, the change of variables `z = 2ⁿ • y`, and the logarithmic
form of the whole-plane covariance kernel `wholePlaneCov` for `‖w‖ ≤ 1`, plus local integrability of `log ‖·‖`.
-/

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- The dilated test function `κₙ k (y) = 4ⁿ k (2ⁿ • y)`: `(g(·/2ⁿ), k) = (g, κₙ k)` for a field `g`
(substitute `x = 2ⁿ y`). -/
noncomputable def dilateTest (n : ℕ) (k : ℂ → ℝ) (y : ℂ) : ℝ :=
  (4 : ℝ) ^ n * k (((2 : ℝ) ^ n) • y)

/-- `κₙ` maps test functions to test functions (smoothness and compact support are preserved by the
linear dilation `y ↦ 2ⁿ • y`). -/
theorem isTestFunction_dilateTest {k : ℂ → ℝ} (hk : IsTestFunction univ k) (n : ℕ) :
    IsTestFunction univ (dilateTest n k) := by
  obtain ⟨h1, h2, -⟩ := hk
  refine ⟨contDiff_const.mul (h1.comp (contDiff_id.const_smul ((2 : ℝ) ^ n))), ?_, subset_univ _⟩
  have hc : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  have h3 : HasCompactSupport (fun y : ℂ => k (((2 : ℝ) ^ n) • y)) :=
    h2.comp_homeomorph (Homeomorph.smulOfNeZero ((2 : ℝ) ^ n) hc)
  exact h3.mul_left

/-- Change of variables `z = 2ⁿ • y`: `∫ κₙ k(y) F(y) dy = ∫ k(z) F(2⁻ⁿ • z) dz` for every function `F`. -/
theorem integral_dilateTest_mul (n : ℕ) (k F : ℂ → ℝ) :
    ∫ y, dilateTest n k y * F y = ∫ z, k z * F (((2 : ℝ) ^ n)⁻¹ • z) := by
  have hc0 : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  have hc2 : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  set G : ℂ → ℝ := fun z => k z * F (((2 : ℝ) ^ n)⁻¹ • z) with hG
  have key : ∀ y : ℂ, dilateTest n k y * F y = (4 : ℝ) ^ n * G (((2 : ℝ) ^ n) • y) := by
    intro y
    simp only [hG, dilateTest, inv_smul_smul₀ hc0]
    ring
  have hscale := Measure.integral_comp_smul (volume : Measure ℂ) G ((2 : ℝ) ^ n)
  rw [Complex.finrank_real_complex, hc2] at hscale
  calc ∫ y, dilateTest n k y * F y = ∫ y, (4 : ℝ) ^ n * G (((2 : ℝ) ^ n) • y) := by
        congr 1; funext y; exact key y
    _ = (4 : ℝ) ^ n * ∫ y, G (((2 : ℝ) ^ n) • y) := integral_const_mul _ _
    _ = (4 : ℝ) ^ n * (|((4 : ℝ) ^ n)⁻¹| • ∫ z, G z) := by rw [hscale]
    _ = ∫ z, G z := by
        rw [abs_of_nonneg (by positivity), smul_eq_mul, ← mul_assoc,
          mul_inv_cancel₀ (by positivity), one_mul]
    _ = ∫ z, k z * F (((2 : ℝ) ^ n)⁻¹ • z) := rfl

/-- Mean zero is preserved by `κₙ`: `∫ κₙ k = ∫ k`. -/
theorem integral_dilateTest (n : ℕ) (k : ℂ → ℝ) :
    ∫ y, dilateTest n k y = ∫ z, k z := by
  simpa using integral_dilateTest_mul n k (fun _ => (1 : ℝ))

/-- For `‖w‖ ≤ 1` and `x ≠ w`, the whole-plane covariance kernel is `log (max ‖x‖ 1) - log ‖x - w‖`
(`wholePlaneCov`, eq:cov-kernel; the factor `max ‖w‖ 1 = 1` drops out). -/
theorem wholePlaneCov_of_norm_le_one {x w : ℂ} (hw : ‖w‖ ≤ 1) (hxw : x ≠ w) :
    wholePlaneCov x w = Real.log (max ‖x‖ 1) - Real.log ‖x - w‖ := by
  have hM : (0 : ℝ) < max ‖x‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hd : ‖x - w‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hxw)
  unfold wholePlaneCov
  rw [max_eq_right hw, mul_one, Real.log_div hM.ne' hd]

/-- `|log r| ≤ 2 r^(-1/2)` for `0 < r ≤ 1`. -/
theorem abs_log_le_rpow_neg_half {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    |Real.log r| ≤ 2 * r ^ (-(1 / 2 : ℝ)) := by
  rw [abs_of_nonpos (Real.log_nonpos hr0.le hr1)]
  have h := Real.log_le_rpow_div (x := r⁻¹) (ε := 1 / 2) (by positivity) (by norm_num)
  rw [Real.log_inv, Real.inv_rpow hr0.le, ← Real.rpow_neg hr0.le] at h
  linarith

/-- Pointwise bound for `log ‖·‖` on a ball of radius `T`, with the exponent `-1/2` (integrable in `ℂ`). -/
theorem norm_log_norm_le_rpow {T : ℝ} (hT : 0 < T) {x : ℂ} (hx : ‖x‖ < T) :
    ‖Real.log ‖x‖‖ ≤ (2 + |Real.log T| * T ^ (1 / 2 : ℝ)) * ‖x‖ ^ (-(1 / 2 : ℝ)) := by
  rcases eq_or_lt_of_le (norm_nonneg x) with h0 | hpos
  · rw [← h0]; simp
  set r := ‖x‖ with hr_def
  have hrpow : 0 ≤ r ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hpos.le _
  have hX : 0 ≤ |Real.log T| * T ^ (1 / 2 : ℝ) := by positivity
  have hsplit : (2 + |Real.log T| * T ^ (1 / 2 : ℝ)) * r ^ (-(1 / 2 : ℝ)) =
      2 * r ^ (-(1 / 2 : ℝ)) + |Real.log T| * T ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ)) := by ring
  rw [Real.norm_eq_abs, hsplit]
  rcases le_total r 1 with h1 | h1
  · have := abs_log_le_rpow_neg_half hpos h1
    nlinarith [mul_nonneg hX hrpow]
  · have hlog : 0 ≤ Real.log r := Real.log_nonneg h1
    rw [abs_of_nonneg hlog]
    have hrT : r ≤ T := hx.le
    have hsq : r ^ (1 / 2 : ℝ) ≤ T ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hpos.le hrT (by norm_num)
    have hone : 1 ≤ T ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hpos _), one_mul]
      exact hsq
    have hlogT : Real.log r ≤ |Real.log T| := le_trans (Real.log_le_log hpos hrT) (le_abs_self _)
    have hmain : |Real.log T| ≤ |Real.log T| * (T ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ))) := by
      have := mul_nonneg (abs_nonneg (Real.log T)) (sub_nonneg.2 hone)
      nlinarith
    have e : |Real.log T| * (T ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ))) =
        |Real.log T| * T ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ)) := by ring
    linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hrpow]

/-- `log ‖·‖` is integrable on every ball of `ℂ` centred at `0`. -/
theorem integrableOn_log_norm_ball (T : ℝ) :
    IntegrableOn (fun w : ℂ => Real.log ‖w‖) (ball 0 T) := by
  rcases le_or_gt T 0 with hT | hT
  · rw [ball_eq_empty.2 (by linarith : T ≤ 0)]
    exact integrableOn_empty
  · refine integrableOn_ball_of_norm_le_rpow (C := 2 + |Real.log T| * T ^ (1 / 2 : ℝ))
      (α := 1 / 2) ?_ ?_ ?_ ?_
    · rw [Complex.finrank_real_complex]; norm_num
    · rw [Complex.finrank_real_complex]; norm_num
    · refine ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_
      exact norm_log_norm_le_rpow hT (mem_ball_zero_iff.1 hx)
    · exact (Measurable.log measurable_norm).aestronglyMeasurable

/-- A test function is integrable on `ℂ`. -/
theorem integrable_of_isTestFunction {k : ℂ → ℝ} (hk : IsTestFunction univ k) : Integrable k :=
  hk.1.continuous.integrable_of_hasCompactSupport hk.2.1

/-- For a test function `k` supported in `closedBall 0 R`, `z ↦ k z * log ‖z - p‖` is integrable for every
centre `p` (translate of `integrableOn_log_norm_ball`, times a bounded factor). -/
theorem integrable_mul_log_norm_sub {k : ℂ → ℝ} (hk : IsTestFunction univ k) {R : ℝ}
    (hR : ∀ z, k z ≠ 0 → ‖z‖ ≤ R) (p : ℂ) :
    Integrable (fun z => k z * Real.log ‖z - p‖) := by
  set T : ℝ := |R| + ‖p‖ + 1 with hT_def
  have hf0 : Integrable (Set.indicator (ball (0 : ℂ) T) fun w : ℂ => Real.log ‖w‖) :=
    (integrableOn_log_norm_ball T).integrable_indicator measurableSet_ball
  have hsh := hf0.comp_sub_right p
  obtain ⟨C, hC⟩ := hk.1.continuous.bounded_above_of_compact_support hk.2.1
  have hmain := hsh.bdd_mul hk.1.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  refine hmain.congr (Filter.Eventually.of_forall fun z => ?_)
  by_cases hkz : k z = 0
  · simp [hkz]
  · have hz : ‖z‖ ≤ R := hR z hkz
    have hzp : z - p ∈ ball (0 : ℂ) T := by
      rw [mem_ball_zero_iff]
      have h1 : ‖z - p‖ ≤ ‖z‖ + ‖p‖ := norm_sub_le _ _
      have h2 : R ≤ |R| := le_abs_self R
      have h3 : 0 ≤ |R| := abs_nonneg R
      linarith
    simp only [Set.indicator_of_mem hzp]

/-- The change of variables gives the dilated covariance of the field: for an integral-zero test function `k`
supported in `closedBall 0 R` and `2ⁿ ≥ R`,
`∫ κₙ k(y) · wholePlaneCov x y dy = -∫ k(z) log ‖x - 2⁻ⁿ • z‖ dz` for every `x`
(`wholePlaneCov` for `‖2⁻ⁿ • z‖ ≤ 1`; the constant `log (max ‖x‖ 1)` integrates to zero). -/
theorem integral_dilateTest_wholePlaneCov {k : ℂ → ℝ} (hk : IsTestFunction univ k) {R : ℝ}
    (hR : ∀ z, k z ≠ 0 → ‖z‖ ≤ R) (hmean : ∫ z, k z = 0) {n : ℕ} (hn : R ≤ (2 : ℝ) ^ n) (x : ℂ) :
    ∫ y, dilateTest n k y * wholePlaneCov x y =
      -∫ z, k z * Real.log ‖x - ((2 : ℝ) ^ n)⁻¹ • z‖ := by
  have hc0 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  rw [integral_dilateTest_mul n k (fun y => wholePlaneCov x y)]
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ ((2 : ℝ) ^ n) • x := by
    rw [ae_iff]; simp [measure_singleton]
  have hpt : ∀ᵐ z ∂(volume : Measure ℂ), k z * wholePlaneCov x (((2 : ℝ) ^ n)⁻¹ • z) =
      Real.log (max ‖x‖ 1) * k z - k z * Real.log ‖x - ((2 : ℝ) ^ n)⁻¹ • z‖ := by
    filter_upwards [hae] with z hz
    by_cases hkz : k z = 0
    · simp [hkz]
    · have hzn : ‖((2 : ℝ) ^ n)⁻¹ • z‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc0), inv_mul_le_iff₀ hc0, mul_one]
        exact (hR z hkz).trans hn
      have hxw : x ≠ ((2 : ℝ) ^ n)⁻¹ • z := by
        intro h; apply hz; rw [h, smul_inv_smul₀ hc0.ne']
      rw [wholePlaneCov_of_norm_le_one hzn hxw]; ring
  rw [integral_congr_ae hpt]
  have hI : Integrable k := integrable_of_isTestFunction hk
  have hint2 : Integrable (fun z => k z * Real.log ‖x - ((2 : ℝ) ^ n)⁻¹ • z‖) := by
    refine ((integrable_mul_log_norm_sub hk hR (((2 : ℝ) ^ n) • x)).sub
      (hI.mul_const (Real.log ((2 : ℝ) ^ n)))).congr ?_
    filter_upwards [hae] with z hz
    by_cases hkz : k z = 0
    · simp [hkz]
    · have hN : x - ((2 : ℝ) ^ n)⁻¹ • z = -(((2 : ℝ) ^ n)⁻¹ • (z - ((2 : ℝ) ^ n) • x)) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]; abel
      have hNz : z - ((2 : ℝ) ^ n) • x ≠ 0 := sub_ne_zero.2 hz
      have hlog : Real.log ‖x - ((2 : ℝ) ^ n)⁻¹ • z‖ = -Real.log ((2 : ℝ) ^ n) + Real.log ‖z - ((2 : ℝ) ^ n) • x‖ := by
        rw [hN, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc0),
          Real.log_mul (inv_ne_zero hc0.ne') (norm_ne_zero_iff.2 hNz), Real.log_inv]
      simp only [Pi.sub_apply]
      rw [hlog]; ring
  have hint1 : Integrable (fun z => Real.log (max ‖x‖ 1) * k z) := hI.const_mul _
  rw [integral_sub hint1 hint2, integral_const_mul, hmean, mul_zero, zero_sub]

end HarmonicBalls
