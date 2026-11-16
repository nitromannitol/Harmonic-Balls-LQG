import HarmonicBalls.Proofs.Potential.LBMClockExit

/-! # Expected exit time under a time-change clock

The expected exit time is the expected clock value at Brownian exit.
-/

namespace HarmonicBalls

open MeasureTheory MarkovProcess Set
open scoped ENNReal NNReal

/-- For an almost surely valid clock, the expected time-changed exit is the
expected clock value at Brownian exit from a bounded open set. -/
theorem expectedLBMExitTime_eq_lintegral_clockValue
    (F : ContinuousPath ℂ → ℝ≥0 → ℝ) (D : Set ℂ) (x : ℂ)
    (hD : IsOpen D) (hbounded : Bornology.IsBounded D)
    (hF : ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F b)) :
    expectedLBMExitTime F D x =
      ∫⁻ b, ENNReal.ofReal (F b (ContinuousPath.exitTime D b).toNNReal)
        ∂(planarBrownianMotion x) := by
  unfold expectedLBMExitTime
  apply lintegral_congr_ae
  filter_upwards [hF, Section6.ae_planarBrownian_exitTime_bounded_lt_top x hbounded] with b hb hfin
  simpa only [ENNReal.ofReal] using lbmExitTime_eq_clockValue hD hb (ne_of_lt hfin)

end HarmonicBalls
