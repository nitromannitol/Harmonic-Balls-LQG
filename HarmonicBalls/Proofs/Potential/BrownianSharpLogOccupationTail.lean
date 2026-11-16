import HarmonicBalls.Proofs.Potential.BrownianSharpLogOccupation

/-! # Brownian occupation tail bound

Unit-time planar Brownian occupation of a ball satisfies a logarithmic tail bound.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Metric
open scoped Interval NNReal ENNReal

namespace HarmonicBalls

/-- Unit-time occupation tails are controlled by the logarithmic endpoint moment bound. -/
theorem planarBrownianMotion_occupation_tail_le_log_kernel (x z : ℂ) (n : ℕ) {r : ℝ}
    (hr : 0 < r) (ha1 : (2 / Real.pi) * (2 * r) ^ 2 ≤ 1)
    (ε : ℝ≥0∞) (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    let a := (2 / Real.pi) * (2 * r) ^ 2
    planarBrownianMotion x {b | ε ≤ ν {t | ‖b t - z‖ < r}} ≤
      ((Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ≥0∞) *
        ENNReal.ofReal (2 * (a * (1 + Real.log (1 / a)))) ^ n) / ε ^ (n + 1) := by
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hm : Measurable (fun b : ContinuousPath ℂ => (ν {t | ‖b t - z‖ < r}) ^ (n + 1)) :=
    (measurable_ball_occupation z r ν).pow_const _
  calc
    _ ≤ planarBrownianMotion x {b | ε ^ (n + 1) ≤ (ν {t | ‖b t - z‖ < r}) ^ (n + 1)} := by
      apply measure_mono
      intro b hb
      change ε ≤ ν {t | ‖b t - z‖ < r} at hb
      exact pow_le_pow_left₀ (show (0 : ℝ≥0∞) ≤ ε from zero_le) hb _
    _ ≤ (∫⁻ b : ContinuousPath ℂ, (ν {t | ‖b t - z‖ < r}) ^ (n + 1)
        ∂(planarBrownianMotion x)) / ε ^ (n + 1) :=
      meas_ge_le_lintegral_div hm.aemeasurable (pow_ne_zero _ hε0) (ENNReal.pow_ne_top hεtop)
    _ ≤ _ := by
      gcongr
      exact planarBrownianMotion_occupation_moment_le_log_kernel x z n hr ha1

end HarmonicBalls
