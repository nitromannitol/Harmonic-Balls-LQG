import Mathlib
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.Laplacian
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleAverageSmoothTestConvergence
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleTestFubiniLimit
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleTestIntegralL2Limit
import HarmonicBalls.Proofs.Sec11.ClosureScales.GaussianCircleTestIntegral
import HarmonicBalls.Proofs.Sec11.ClosureScales.RouteAKernelBox

/-!
# Linear rate for the circle averages of a smooth test function

Let `φ : ℂ → ℝ` be a test function on `ℂ` (`IsTestFunction Set.univ φ`: smooth with compact support) and write
`φ_r(x) = Real.circleAverage φ x r` for the average of `φ` over the circle `∂B(x, r)`. For `0 < r ≤ 1` this file
proves the following.

* `exists_abs_circleAverage_sub_le`: `|φ_r(x) - φ(x)| ≤ C r` for every `x ∈ ℂ`.
* `exists_integral_sq_circleAverage_sub_le`: `∫ (φ_r - φ)² dx ≤ C r²` for Lebesgue measure on `ℂ`.
* `exists_second_moment_circleTestIntegral_le`: for every whole-plane Gaussian free field `(h^ℂ, h^ℂ_r)`
  (`IsWholePlaneGFF P hC hcirc`) on a measurable space `Ω : Type u`,
  `E[(∫ h^ℂ_r(w) φ(w) dw - h^ℂ(φ))²] ≤ C r²`, with `C` depending only on `φ`.

The first two bounds use the Lipschitz (mean value) inequality of the compactly supported `φ` and a fixed ball that
contains the supports of all `φ_r - φ`, `0 < r ≤ 1`. The third bound applies the fixed-test covariance (Schur)
estimate `abs_wholePlaneGFFCov_pairing_le` to `φ_r - φ`, after the almost-sure identity
`∫ h^ℂ_r φ = h^ℂ(φ_r)`. Only proved providers are used: no literature input, no new carrier and no new hypothesis.
-/

universe u

namespace HarmonicBalls.SmoothCircleAverageRate

open MeasureTheory Set Metric

/-- **Lipschitz bound for a test function.** A test function `φ` on `ℂ` is globally Lipschitz: there is a constant
`L ≥ 0` with `|φ y - φ x| ≤ L ‖y - x‖` for all `x, y ∈ ℂ`. The derivative is bounded because it is continuous and
compactly supported, and the mean value inequality on the convex set `ℂ` gives the bound. -/
lemma exists_lipschitz_of_isTestFunction {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℂ, |φ y - φ x| ≤ L * ‖y - x‖ := by
  have hsm := hφ.1
  have hcont : Continuous (fderiv ℝ φ) := hsm.continuous_fderiv (by norm_num)
  have hsupp : HasCompactSupport (fderiv ℝ φ) := hφ.2.1.fderiv (𝕜 := ℝ)
  obtain ⟨L, hL⟩ := hcont.bounded_above_of_compact_support hsupp
  refine ⟨max L 0, le_max_right _ _, fun x y => ?_⟩
  have hdiff : ∀ z ∈ (univ : Set ℂ), DifferentiableAt ℝ φ z := fun z _ =>
    hsm.differentiable (by simp) z
  have hbound : ∀ z ∈ (univ : Set ℂ), ‖fderiv ℝ φ z‖ ≤ max L 0 := fun z _ =>
    (hL z).trans (le_max_left _ _)
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound convex_univ
    (mem_univ x) (mem_univ y)
  rwa [Real.norm_eq_abs] at h

/-- **Oscillation of a Lipschitz function on a circle.** If `φ` satisfies `|φ y - φ x| ≤ L ‖y - x‖`, then
`|φ_r(x) - φ(x)| ≤ L r` for every centre `x` and every radius `r > 0`: every point of the circle is at distance `r`
from the centre, and the circle average of the continuous function `φ - φ(x)` is bounded by its sup on the circle. -/
lemma abs_circleAverage_sub_le_of_lipschitz {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) {L : ℝ}
    (hL : ∀ x y : ℂ, |φ y - φ x| ≤ L * ‖y - x‖) {r : ℝ} (hr : 0 < r) (x : ℂ) :
    |Real.circleAverage φ x r - φ x| ≤ L * r := by
  have key : ∀ θ : ℝ, ‖φ (circleMap x r θ) - φ x‖ ≤ L * r := by
    intro θ
    have hd : ‖circleMap x r θ - x‖ = r := by
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
    rw [Real.norm_eq_abs]
    calc |φ (circleMap x r θ) - φ x| ≤ L * ‖circleMap x r θ - x‖ := hL x _
      _ = L * r := by rw [hd]
  have h := CircleTestFubini.norm_circleAverage_sub_le hφ.1.continuous x key
  rwa [Real.norm_eq_abs] at h

/-- **Linear rate, pointwise.** For a test function `φ` there is a finite constant `C ≥ 0` with
`|φ_r(x) - φ(x)| ≤ C r` for every `x ∈ ℂ` and every radius `0 < r ≤ 1`. -/
theorem exists_abs_circleAverage_sub_le {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x : ℂ,
      |Real.circleAverage φ x r - φ x| ≤ C * r := by
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_of_isTestFunction hφ
  exact ⟨L, hL0, fun r hr _ x => abs_circleAverage_sub_le_of_lipschitz hφ hL hr x⟩

/-- **Linear rate in `L²(dx)`.** For a test function `φ` there is a finite constant `C ≥ 0` with
`∫ (φ_r - φ)² dx ≤ C r²` for every `0 < r ≤ 1`. The integrand vanishes outside one fixed ball
(`CircleTestIntegralL2Limit.exists_ball_circleAverage_sub_eq_zero`), so the squared sup bound integrates to
`L² r² vol(ball 0 M)`. -/
theorem exists_integral_sq_circleAverage_sub_le {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∫ x, (Real.circleAverage φ x r - φ x) ^ 2 ≤ C * r ^ 2 := by
  obtain ⟨L, -, hL⟩ := exists_lipschitz_of_isTestFunction hφ
  obtain ⟨M, hzero⟩ := CircleTestIntegralL2Limit.exists_ball_circleAverage_sub_eq_zero hφ
  refine ⟨L ^ 2 * (volume (ball (0 : ℂ) M)).toReal, mul_nonneg (sq_nonneg L) ENNReal.toReal_nonneg,
    fun r hr hr1 => ?_⟩
  have h := CircleTestIntegralL2Limit.integral_sq_le_of_bound
    (f := fun x => Real.circleAverage φ x r - φ x) (M := M) (δ := L * r)
    (fun x hx => hzero r hr hr1 x hx) (fun x => abs_circleAverage_sub_le_of_lipschitz hφ hL hr x)
  calc ∫ x, (Real.circleAverage φ x r - φ x) ^ 2
      ≤ (L * r) ^ 2 * (volume (ball (0 : ℂ) M)).toReal := h
    _ = L ^ 2 * (volume (ball (0 : ℂ) M)).toReal * r ^ 2 := by ring

/-- **Fixed-test Schur bound for the circle-average test integral.** Let `(h^ℂ, h^ℂ_r)` be a whole-plane GFF, let `φ` be a
test function, and let `0 < r ≤ 1`. Suppose `φ_r - φ` vanishes outside the ball `B(0, M)` and is bounded by `B`. Then
`E[(∫ h^ℂ_r(w) φ(w) dw - h^ℂ(φ))²] ≤ (2 · kernelBoxConst M).toReal · ∫ (φ_r - φ)² dx`, where the constant is finite
since `kernelBoxConst M < ⊤` (`kernelBoxConst_lt_top`). The almost-sure identity
`∫ h^ℂ_r φ = h^ℂ(φ_r)` (`IsWholePlaneGFF.ae_integral_circle_mul_eq_pairing_circleAverage`) turns the left side into the
second moment of `h^ℂ(φ_r) - h^ℂ(φ)`, which is the covariance kernel at the fixed test `φ_r - φ`
(`IsWholePlaneGFF.integral_sq_sub_pairing`), and the Schur estimate `abs_wholePlaneGFFCov_pairing_le` bounds that. -/
theorem circleTestIntegral_second_moment_le_schur {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc)
    {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) {r M B : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hzero : ∀ x : ℂ, x ∉ ball (0 : ℂ) M → Real.circleAverage φ x r - φ x = 0)
    (hB : ∀ x : ℂ, |Real.circleAverage φ x r - φ x| ≤ B) :
    ∫ ω, ((∫ w, hcirc ω r w * φ w) - hC ω φ) ^ 2 ∂P
      ≤ (2 * kernelBoxConst M).toReal * ∫ x, (Real.circleAverage φ x r - φ x) ^ 2 := by
  have hψ : IsTestFunction univ (fun v => Real.circleAverage φ v r) :=
    CircleTestFubini.isTestFunction_univ_circleAverage hφ (by rw [abs_of_pos hr]; exact hr1)
  have hf : IsTestFunction univ (fun x => Real.circleAverage φ x r - φ x) :=
    CircleTestIntegralL2Limit.isTestFunction_univ_sub hψ hφ
  have hEq : ∫ ω, ((∫ w, hcirc ω r w * φ w) - hC ω φ) ^ 2 ∂P
      = ∫ ω, (hC ω (fun v => Real.circleAverage φ v r) - hC ω φ) ^ 2 ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hgff.ae_integral_circle_mul_eq_pairing_circleAverage hφ hr hr1] with ω hω
    rw [hω.2]
  have hS := abs_wholePlaneGFFCov_pairing_le (M := M) (B := B)
    (f := fun x => Real.circleAverage φ x r - φ x) hf.1.continuous.measurable hzero hB
  rw [hEq, hgff.integral_sq_sub_pairing hψ hφ]
  exact le_trans (le_abs_self _) hS

/-- **Linear second-moment rate for the circle-average test integrals.** Let `φ` be a test function on `ℂ`. There is a
finite constant `C ≥ 0`, depending only on `φ`, such that for every measurable space `Ω : Type u`, every measure `P` on `Ω`,
every whole-plane Gaussian free field `(h^ℂ, h^ℂ_r)` with `IsWholePlaneGFF P hC hcirc`, and every radius `0 < r ≤ 1`:
`E[(∫ h^ℂ_r(w) φ(w) dw - h^ℂ(φ))²] ≤ C r²`. -/
theorem exists_second_moment_circleTestIntegral_le {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        ∫ ω, ((∫ w, hcirc ω r w * φ w) - hC ω φ) ^ 2 ∂P ≤ C * r ^ 2 := by
  obtain ⟨M, hzero⟩ := CircleTestIntegralL2Limit.exists_ball_circleAverage_sub_eq_zero hφ
  obtain ⟨C₁, -, hC₁⟩ := exists_abs_circleAverage_sub_le hφ
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_integral_sq_circleAverage_sub_le hφ
  refine ⟨(2 * kernelBoxConst M).toReal * C₂, mul_nonneg ENNReal.toReal_nonneg hC₂0, ?_⟩
  intro Ω _ P hC hcirc hgff r hr hr1
  have hS := circleTestIntegral_second_moment_le_schur hgff hφ (M := M) (B := C₁ * r) hr hr1
    (fun x hx => hzero r hr hr1 x hx) (fun x => hC₁ r hr hr1 x)
  calc ∫ ω, ((∫ w, hcirc ω r w * φ w) - hC ω φ) ^ 2 ∂P
      ≤ (2 * kernelBoxConst M).toReal * ∫ x, (Real.circleAverage φ x r - φ x) ^ 2 := hS
    _ ≤ (2 * kernelBoxConst M).toReal * (C₂ * r ^ 2) :=
        mul_le_mul_of_nonneg_left (hC₂ r hr hr1) ENNReal.toReal_nonneg
    _ = (2 * kernelBoxConst M).toReal * C₂ * r ^ 2 := by ring

end HarmonicBalls.SmoothCircleAverageRate
