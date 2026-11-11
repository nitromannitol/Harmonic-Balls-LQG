import HarmonicBalls.FirstPass.S11i.DilationMixing

/-!
# Step 8 helper: the logarithmic potential of a test function is continuous

Source: corrected paper, lemma `s11-pinch:lem:mixing` (tex lines 3769-3812), used in the covariance decay
`Cov((g, f), (𝒯ⁿ g, k)) → 0` (Armitage-Gardiner, potential theory of `log|·|`: `log|·|` is locally integrable
on `ℂ`, so its convolution with a test function is continuous).

For a test function `f`, `G_f(w) = ∫ f x log ‖x - w‖ dx` equals the convolution `log‖·‖ ⋆ f` (substitute `x = w - t`).
-/

open MeasureTheory Filter Topology Metric Set
open scoped ContinuousLinearMap Convolution

namespace HarmonicBalls

/-- `log ‖·‖` is locally integrable on `ℂ`. -/
theorem locallyIntegrable_log_norm_complex :
    LocallyIntegrable (fun w : ℂ => Real.log ‖w‖) volume := by
  intro x
  refine ⟨ball 0 (‖x‖ + 1), ?_, integrableOn_log_norm_ball _⟩
  exact isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (by linarith [norm_nonneg x]))

/-- The logarithmic potential of a test function, `w ↦ ∫ f x log ‖x - w‖ dx`, is the convolution of
`log ‖·‖` with `f`; hence it is continuous on `ℂ` (Mathlib `HasCompactSupport.continuous_convolution_right`). -/
theorem continuous_logPotential {f : ℂ → ℝ} (hf : IsTestFunction univ f) :
    Continuous (fun w : ℂ => ∫ x, f x * Real.log ‖x - w‖) := by
  obtain ⟨hC, hcs, -⟩ := hf
  have hconv : (fun w : ℂ => ∫ x, f x * Real.log ‖x - w‖)
      = (fun t : ℂ => Real.log ‖t‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f := by
    funext w
    rw [convolution_def]
    have h1 := integral_sub_left_eq_self (fun x => f x * Real.log ‖x - w‖) volume w
    simp only [sub_sub_cancel_left, norm_neg] at h1
    rw [← h1]
    congr 1
    funext t
    simp [mul_comm]
  rw [hconv]
  exact HasCompactSupport.continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hcs
    locallyIntegrable_log_norm_complex hC.continuous

end HarmonicBalls
