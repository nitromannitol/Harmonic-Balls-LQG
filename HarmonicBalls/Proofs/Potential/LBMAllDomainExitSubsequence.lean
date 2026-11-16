import HarmonicBalls.Proofs.Potential.LQGClockUniformSubsequence
import HarmonicBalls.Proofs.Potential.LBMExitApproximation

/-! # Simultaneous approximation of exit times

One deterministic subsequence approximates the time-changed exit time almost
surely for every bounded open domain simultaneously.
-/

namespace HarmonicBalls

open MeasureTheory MarkovProcess Filter Topology Set
open scoped ENNReal NNReal

/-- One dyadic subsequence converges at Brownian exit to the time-changed exit
simultaneously for all bounded open domains. -/
theorem IsLQGClock.exists_seq_tendsto_clockApprox_lbmExitTime_all_domains
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hclock : IsLQGClock planarBrownianMotion γ hε x F)
    (hF : ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F b)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      ∀ᵐ b ∂(planarBrownianMotion x), ∀ D : Set ℂ,
        IsOpen D → Bornology.IsBounded D →
        Tendsto (fun n => lqgClockApprox γ hε (dyadicScale (s n)) b
          (ContinuousPath.exitTime D b).toNNReal) atTop
          (𝓝 (lbmExitTime F D b).toReal) := by
  obtain ⟨s, hs, hconv⟩ := hclock.exists_seq_locally_uniform_clockApprox
  have hballs : ∀ᵐ b ∂(planarBrownianMotion x), ∀ n : ℕ,
      ContinuousPath.exitTime (Metric.ball x (n : ℝ)) b < ∞ := by
    simp only [ae_all_iff]
    exact fun n => Section6.ae_planarBrownianMotion_exitTime_ball_lt_top x n
  refine ⟨s, hs, ?_⟩
  filter_upwards [hconv, hF, hballs] with b hb hf hball
  intro D hD hbounded
  obtain ⟨R, hR⟩ := hbounded.subset_ball x
  obtain ⟨n, hn⟩ := exists_nat_ge R
  have hsub : D ⊆ Metric.ball x (n : ℝ) :=
    hR.trans (Metric.ball_subset_ball hn)
  have hfin : ContinuousPath.exitTime D b < ∞ :=
    lt_of_le_of_lt (ContinuousPath.exitTime_mono hsub b) (hball n)
  have heq : (lbmExitTime F D b).toReal = F b (ContinuousPath.exitTime D b).toNNReal := by
    rw [lbmExitTime_eq_clockValue hD hf (ne_of_lt hfin)]
    have hnneg : 0 ≤ F b (ContinuousPath.exitTime D b).toNNReal := by
      simpa only [hf.map_zero] using hf.strictMono.monotone
        (show (0 : ℝ≥0) ≤ (ContinuousPath.exitTime D b).toNNReal from bot_le)
    simp [hnneg]
  rw [heq, Metric.tendsto_nhds]
  intro ε hεpos
  filter_upwards [hb (ContinuousPath.exitTime D b).toNNReal ε hεpos] with n hn
  simpa only [Real.dist_eq] using hn _ le_rfl

end HarmonicBalls
