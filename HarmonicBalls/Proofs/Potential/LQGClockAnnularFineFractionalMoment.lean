import HarmonicBalls.Proofs.Potential.LQGClockAnnularSecondMoment
import LatticeProb.LQG.LQGMassMoment

/-! # Fine-scale moments of inserted circle averages

The moment of the inserted density at a point has an explicit dependence on
its smoothing scale and the insertion point.
-/

open MeasureTheory
open scoped ENNReal

namespace HarmonicBalls

/-- The one-point moment of the inserted density at a circle contained in the
unit disc. -/
theorem lintegral_inserted_clock_density_rpow_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ}
    (hε : 0 < ε) {z : ℂ} (hz : ‖z‖ + ε ≤ 1) (γ α : ℝ)
    {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ ω, (ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) ^ p ∂P) =
      ENNReal.ofReal (Real.exp (-(p * γ * α) * Real.log (max ε ‖z‖))) *
        ENNReal.ofReal (ε ^ (-(γ ^ 2 * p * (p - 1) / 2))) := by
  have hmeas : Measurable (fun ω =>
      (ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z))) ^ p) :=
    (Measurable.ennreal_ofReal ((measurable_const.mul
      (Real.measurable_exp.comp ((hh.measurable_circle ε z hε).const_mul γ))))).pow_const p
  have heq : ∀ᵐ ω ∂P,
      (ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) ^ p =
      ENNReal.ofReal (Real.exp (-(p * γ * α) * Real.log (max ε ‖z‖))) *
        (ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z))) ^ p := by
    filter_upwards [ae_recentered_inserted_circle_average hh α,
      hh.ae_circleAverage_one_zero] with ω hω hzero
    rw [← hω ε z hε, hzero]
    simp only [sub_zero]
    have hsplit : γ * (hcirc ω ε z - α * Real.log (max ε ‖z‖)) =
        γ * hcirc ω ε z + (-(γ * α) * Real.log (max ε ‖z‖)) := by ring
    rw [hsplit, Real.exp_add]
    have hfactor : ε ^ (γ ^ 2 / 2) *
        (Real.exp (γ * hcirc ω ε z) * Real.exp (-(γ * α) * Real.log (max ε ‖z‖))) =
        Real.exp (-(γ * α) * Real.log (max ε ‖z‖)) *
          (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z)) := by ring
    rw [hfactor, ENNReal.ofReal_mul (by positivity), ENNReal.mul_rpow_of_nonneg _ _ hp,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hp, ← Real.exp_mul]
    congr 3
    ring
  rw [lintegral_congr_ae heq, lintegral_const_mul _ hmeas,
    hh.lintegral_rpow_mul_exp_circle hε hz (γ ^ 2 / 2) γ hp]
  congr 2
  ring

end HarmonicBalls
