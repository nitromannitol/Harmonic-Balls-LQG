import HarmonicBalls.Defs.LBM
import HarmonicBalls.Proofs.Potential.GreenOccupationCharacterization

/-! # Occupation identity for the regularized Liouville clock

The expected nonnegative finite-scale clock is the killed Brownian occupation
integral of its exponential density, and hence its Green-density integral.
-/

open MeasureTheory Set MarkovProcess
open scoped ENNReal NNReal

namespace HarmonicBalls.GreenOccupation

/-- The nonnegative image of the real finite-scale clock at the Brownian exit
 time has the killed occupation integral and Green-density representations. -/
theorem lintegral_lqgClockApprox_exit_eq_occupation_and_green
    {D : Set ℂ} (hD : IsSmoothBoundedOpen D) {x : ℂ} (hx : x ∈ D)
    (γ ε : ℝ) (hε : 0 < ε) (hεfield : ℝ → ℂ → ℝ)
    (hcont : Continuous (hεfield ε)) :
    (∫⁻ p, ENNReal.ofReal (lqgClockApprox γ hεfield ε p
      (ContinuousPath.exitTime D p).toNNReal) ∂planarBrownianMotion x) =
      (∫⁻ y, ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hεfield ε y))
        ∂occupationMeasure D (GreenGeneral.isOpen_of_isSmoothBoundedOpen hD) x) ∧
    (∫⁻ p, ENNReal.ofReal (lqgClockApprox γ hεfield ε p
      (ContinuousPath.exitTime D p).toNNReal) ∂planarBrownianMotion x) =
      ∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) *
        ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hεfield ε y)) := by
  let g : ℂ → ℝ := fun y => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hεfield ε y)
  have hg : Continuous g := continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hcont))
  have hg0 : ∀ y, 0 ≤ g y := fun y =>
    mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le
  let hDo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  have hocc := lintegral_occupationMeasure_eq_stopped_integral hDo hD.1 x hg hg0
  have hgreen := lintegral_brownian_occupation_eq_green_integral hD hx hg.measurable.ennreal_ofReal
  have hbefore := lintegral_occupationMeasure hDo x hg.measurable.ennreal_ofReal
  constructor
  · simpa only [lqgClockApprox, g] using hocc.symm
  · calc
      _ = ∫⁻ y, ENNReal.ofReal (g y) ∂occupationMeasure D hDo x := by
        simpa only [lqgClockApprox, g] using hocc.symm
      _ = _ := hbefore.trans hgreen

end HarmonicBalls.GreenOccupation
