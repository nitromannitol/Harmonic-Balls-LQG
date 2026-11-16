import HarmonicBalls.Proofs.Potential.LBMExitApproximation
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Almost-sure approximation of time-changed exit times

A deterministic subsequence of the dyadic clock values at Brownian exit
converges almost surely to the time-changed exit time.
-/

namespace HarmonicBalls

open MeasureTheory MarkovProcess Filter Topology Set
open scoped ENNReal NNReal

/-- A subsequence of dyadic clock values at Brownian exit converges almost surely
 to the Liouville Brownian exit time for an almost surely valid clock. -/
theorem IsLQGClock.exists_seq_tendsto_clockApprox_lbmExitTime
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {D : Set ℂ}
    (hclock : IsLQGClock planarBrownianMotion γ hε x F)
    (hD : IsOpen D) (hbounded : Bornology.IsBounded D)
    (hF : ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F b)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      ∀ᵐ b ∂(planarBrownianMotion x),
        Tendsto (fun n => lqgClockApprox γ hε (dyadicScale (s n)) b
          (ContinuousPath.exitTime D b).toNNReal) atTop
          (𝓝 (lbmExitTime F D b).toReal) := by
  have hconv : TendstoInMeasure (planarBrownianMotion x)
      (fun k b => lqgClockApprox γ hε (dyadicScale k) b
        (ContinuousPath.exitTime D b).toNNReal) atTop
      (fun b => (lbmExitTime F D b).toReal) := by
    apply tendstoInMeasure_iff_dist.mpr
    intro η hη
    simpa only [Real.dist_eq] using
      hclock.tendsto_measure_clockApprox_lbmExitTime hD hbounded hF hη
  exact hconv.exists_seq_tendsto_ae

end HarmonicBalls
