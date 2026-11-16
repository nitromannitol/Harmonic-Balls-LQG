import HarmonicBalls.Proofs.Potential.LQGClockUniqueness

/-! # Independence of Liouville Brownian exit times from the clock version

Clocks for the same Brownian law and field give the same exit times almost
surely, simultaneously for all domains, and the same expected exit times.
-/

namespace HarmonicBalls

open MeasureTheory MarkovProcess Filter
open scoped ENNReal NNReal

/-- Two versions of the clock give the same exit times simultaneously for every domain. -/
theorem IsLQGClock.ae_lbmExitTime_eq {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F G : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : IsLQGClock planarBrownianMotion γ hε x F)
    (hG : IsLQGClock planarBrownianMotion γ hε x G) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ D : Set ℂ, lbmExitTime F D b = lbmExitTime G D b := by
  filter_upwards [hF.ae_eq hG] with b hb
  have h : F b = G b := funext hb
  intro D
  change pathExitTime D (fun t => b (clockInverse (F b) t)) =
    pathExitTime D (fun t => b (clockInverse (G b) t))
  exact congrArg (fun f => pathExitTime D (fun t => b (clockInverse f t))) h

/-- The expected exit time does not depend on the version of the clock. -/
theorem IsLQGClock.expectedLBMExitTime_eq {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F G : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : IsLQGClock planarBrownianMotion γ hε x F)
    (hG : IsLQGClock planarBrownianMotion γ hε x G) (D : Set ℂ) :
    expectedLBMExitTime F D x = expectedLBMExitTime G D x := by
  unfold expectedLBMExitTime
  exact lintegral_congr_ae ((hF.ae_lbmExitTime_eq hG).mono fun b hb => hb D)

end HarmonicBalls
