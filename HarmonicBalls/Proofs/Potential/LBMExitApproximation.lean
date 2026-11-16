import HarmonicBalls.Proofs.Potential.LQGClockApproxExit
import HarmonicBalls.Proofs.Potential.LBMClockExit

/-! # Approximation of time-changed exit times

The dyadic clock values at Brownian exit converge in probability to the
exit time of the time-changed path.
-/

namespace HarmonicBalls

open MeasureTheory MarkovProcess Filter Topology Set
open scoped ENNReal NNReal

/-- Dyadic clock values at Brownian exit converge in probability to the
Liouville Brownian exit time for an almost surely valid clock. -/
theorem IsLQGClock.tendsto_measure_clockApprox_lbmExitTime
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {D : Set ℂ}
    (hclock : IsLQGClock planarBrownianMotion γ hε x F)
    (hD : IsOpen D) (hbounded : Bornology.IsBounded D)
    (hF : ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F b))
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun k : ℕ => planarBrownianMotion x
      {b | η ≤ |lqgClockApprox γ hε (dyadicScale k) b
        (ContinuousPath.exitTime D b).toNNReal - (lbmExitTime F D b).toReal|})
      atTop (𝓝 0) := by
  have heq : ∀ᵐ b ∂(planarBrownianMotion x),
      (lbmExitTime F D b).toReal = F b (ContinuousPath.exitTime D b).toNNReal := by
    filter_upwards [hF, Section6.ae_planarBrownian_exitTime_bounded_lt_top x hbounded] with b hb hfin
    rw [lbmExitTime_eq_clockValue hD hb (ne_of_lt hfin)]
    have hn : 0 ≤ F b (ContinuousPath.exitTime D b).toNNReal := by
      simpa only [hb.map_zero] using hb.strictMono.monotone
        (show (0 : ℝ≥0) ≤ (ContinuousPath.exitTime D b).toNNReal from bot_le)
    simp [hn]
  have hevents : ∀ k : ℕ, planarBrownianMotion x
      {b | η ≤ |lqgClockApprox γ hε (dyadicScale k) b
        (ContinuousPath.exitTime D b).toNNReal - (lbmExitTime F D b).toReal|} =
      planarBrownianMotion x
      {b | η ≤ |lqgClockApprox γ hε (dyadicScale k) b
        (ContinuousPath.exitTime D b).toNNReal - F b (ContinuousPath.exitTime D b).toNNReal|} := by
    intro k
    apply measure_congr
    filter_upwards [heq] with b hb
    simp only [hb]
  simp_rw [hevents]
  exact hclock.tendsto_measure_clockApprox_exitTime hD hbounded hη

end HarmonicBalls
