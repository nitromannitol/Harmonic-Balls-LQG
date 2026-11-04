import HarmonicBalls.Steps.Sec5.ScaleInvariance
import HarmonicBalls.Proofs.Sec2.AffineField

/-! # Normalized LQG measures under rescaling -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- Circle averages of the normalized logarithmically singular field commute
with positive dilations, including the additive circle-average correction. -/
theorem fieldCircleAverage_affineScale (α₀ : ℝ) (hcirc : ℝ → ℂ → ℝ)
    {k r : ℝ} (hk : 0 < k) (hr : 0 < r) (z : ℂ) :
    fieldCircleAverage α₀ (fun s w => hcirc (k * s) (k • w) - hcirc k 0) r z =
      fieldCircleAverage α₀ hcirc (k * r) (k • z) - fieldCircleAverage α₀ hcirc k 0 := by
  rw [fieldCircleAverage_eq _ _ hr, fieldCircleAverage_eq _ _ (mul_pos hk hr),
    fieldCircleAverage_eq _ _ hk]
  simp only [norm_zero, max_eq_left hk.le, norm_smul, Real.norm_eq_abs, abs_of_pos hk]
  rw [← mul_max_of_nonneg _ _ hk.le, Real.log_mul hk.ne' (by positivity)]
  ring

/-- Coordinate change and subtraction of the circle average identify the normalized
pullback as the LQG measure of the scaled field, also with a logarithmic singularity. -/
theorem isLQGMeasureOfField_normalizedPullback {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {k : ℝ} (hk : 0 < k) :
    IsLQGMeasureOfField P γ α₀
      (fun ω r z => hcirc ω (k * r) (k • z) - hcirc ω k 0)
      (fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) := by
  filter_upwards [hCC hGFF hγ hγ2 hα μ hμ] with ω hω
  let c := lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0
  have h := (hω (k : ℂ) (by exact_mod_cast hk.ne') 0).add_const (-c)
  have hmap : (fun x : ℂ => (x - 0) / (k : ℂ)) = (fun x : ℂ => k⁻¹ • x) := by
    funext x
    simp [div_eq_mul_inv, Complex.real_smul, mul_comm]
  have hm : ENNReal.ofReal (Real.exp (γ * -c)) •
      (μ ω).map (fun x : ℂ => (x - 0) / (k : ℂ)) =
      normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω) := by
    rw [hmap]
    simp only [normalizedPullbackMeasure, ← Real.exp_neg, mul_neg]
    rfl
  have hf : ∀ n, lqgApprox γ
      (fun ε z => fieldCircleAverage α₀ (hcirc ω) (‖(k : ℂ)‖ * ε)
        ((k : ℂ) * z + 0) + lqgQ γ * Real.log ‖(k : ℂ)‖ + -c) (dyadicScale n) =
      lqgApprox γ (fieldCircleAverage α₀
        (fun r z => hcirc ω (k * r) (k • z) - hcirc ω k 0)) (dyadicScale n) := by
    intro n
    have hpos : 0 < dyadicScale n := by simp [dyadicScale]
    simp only [lqgApprox]
    congr 1
    funext z
    rw [fieldCircleAverage_affineScale α₀ (hcirc ω) hk hpos]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk, add_zero,
      Complex.real_smul]
    dsimp [c]
    congr 3
    ring
  rw [hm] at h
  refine ⟨h.isLocallyFiniteMeasure, fun f hf' hfc => ?_⟩
  simpa only [hf] using h.tendsto_integral f hf' hfc

end HarmonicBalls
