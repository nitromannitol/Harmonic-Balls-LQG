import HarmonicBalls.Proofs.Sec2.AffineField

/-!
# Shifting dyadic circle-average scales

The dyadic approximation sequence is unchanged after a fixed shift of its indices,
provided that the usual variance-normalization factor is included. This is a
deterministic step toward the dyadic coordinate change for LQG measures.
-/

namespace HarmonicBalls

open MeasureTheory Filter
open scoped Topology

/-- A dyadic scale shifted by `m` becomes the original scale after multiplication
by `2 ^ m`. -/
theorem dyadicScale_shift (m n : ℕ) :
    (2 : ℝ) ^ m * dyadicScale (n + m) = dyadicScale n := by
  simp only [dyadicScale, pow_add]
  have h : (2 : ℝ) ^ m * ((2 : ℝ)⁻¹ ^ m) = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (2 : ℝ) ^ m * ((2 : ℝ)⁻¹ ^ n * (2 : ℝ)⁻¹ ^ m) =
        ((2 : ℝ) ^ m * ((2 : ℝ)⁻¹ ^ m)) * ((2 : ℝ)⁻¹ ^ n) := by ring
    _ = (2 : ℝ)⁻¹ ^ n := by rw [h, one_mul]

/-- A dyadic change of circle-average radius, with its normalization, has
exactly the same vague limit. No spatial coordinate change is used here. -/
theorem IsLQGLimit.dyadic_radius_shift {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    {μ : Measure ℂ} (hμ : IsLQGLimit γ hε μ) (m : ℕ) :
    IsLQGLimit γ (fun r z => hε ((2 : ℝ) ^ m * r) z +
      (γ / 2) * Real.log ((2 : ℝ) ^ m)) μ := by
  let k : ℝ := (2 : ℝ) ^ m
  have hk : 0 < k := by dsimp [k]; positivity
  have happrox (n : ℕ) :
      lqgApprox γ (fun r z => hε (k * r) z + (γ / 2) * Real.log k)
        (dyadicScale (n + m)) = lqgApprox γ hε (dyadicScale n) := by
    have hr : 0 < dyadicScale (n + m) := dyadicScale_pos _
    have hscale : k * dyadicScale (n + m) = dyadicScale n := dyadicScale_shift m n
    simp only [lqgApprox]
    congr 1
    funext z
    rw [← hscale, Real.mul_rpow hk.le hr.le, Real.rpow_def_of_pos hk]
    have hexp : Real.exp (γ * (γ / 2 * Real.log k)) =
        Real.exp (Real.log k * (γ ^ 2 / 2)) := by
      congr 1
      ring
    rw [mul_add, Real.exp_add, hexp]
    ring
  refine ⟨hμ.isLocallyFiniteMeasure, fun f hf hfc => ?_⟩
  apply (tendsto_add_atTop_iff_nat m).1
  change Tendsto (fun n => ∫ z, f z ∂(lqgApprox γ
    (fun r z => hε (k * r) z + (γ / 2) * Real.log k) (dyadicScale (n + m))))
      atTop (𝓝 (∫ z, f z ∂μ))
  simpa only [happrox] using hμ.tendsto_integral f hf hfc

/-- Without the additive normalization, shifting the circle-average radius
multiplies the limiting measure by the corresponding deterministic factor. -/
theorem IsLQGLimit.dyadic_radius_shift_unscaled {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    {μ : Measure ℂ} (hμ : IsLQGLimit γ hε μ) (m : ℕ) :
    IsLQGLimit γ (fun r z => hε ((2 : ℝ) ^ m * r) z)
      (ENNReal.ofReal (Real.exp (-(γ * ((γ / 2) * Real.log ((2 : ℝ) ^ m))))) • μ) := by
  have h := (hμ.dyadic_radius_shift m).add_const (-((γ / 2) * Real.log ((2 : ℝ) ^ m)))
  simpa only [add_neg_cancel_right, mul_neg] using h

end HarmonicBalls
