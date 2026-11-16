import HarmonicBalls.Proofs.Potential.LBMAllDomainExitSubsequence

/-! # Uniform approximation of enclosed-domain exit times

A deterministic subsequence approximates time-changed exit times almost surely,
uniformly over all open domains contained in a fixed ball.
-/

namespace HarmonicBalls

open MeasureTheory MarkovProcess Filter Topology Set
open scoped ENNReal NNReal

/-- One dyadic subsequence approximates time-changed exits uniformly over all
open domains contained in each ball around the starting point. -/
theorem IsLQGClock.exists_seq_uniform_clockApprox_lbmExitTime_enclosed_domains
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hclock : IsLQGClock planarBrownianMotion γ hε x F)
    (hF : ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F b)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      ∀ᵐ b ∂(planarBrownianMotion x), ∀ R η : ℝ, 0 < η →
        ∀ᶠ n in atTop, ∀ D : Set ℂ, IsOpen D → D ⊆ Metric.ball x R →
          |lqgClockApprox γ hε (dyadicScale (s n)) b
            (ContinuousPath.exitTime D b).toNNReal - (lbmExitTime F D b).toReal| < η := by
  obtain ⟨s, hs, hconv⟩ := hclock.exists_seq_locally_uniform_clockApprox
  have hballs : ∀ᵐ b ∂(planarBrownianMotion x), ∀ n : ℕ,
      ContinuousPath.exitTime (Metric.ball x (n : ℝ)) b < ∞ := by
    simp only [ae_all_iff]
    exact fun n => Section6.ae_planarBrownianMotion_exitTime_ball_lt_top x n
  refine ⟨s, hs, ?_⟩
  filter_upwards [hconv, hF, hballs] with b hb hf hball
  intro R η hη
  obtain ⟨m, hm⟩ := exists_nat_ge R
  filter_upwards [hb (ContinuousPath.exitTime (Metric.ball x (m : ℝ)) b).toNNReal η hη] with n hn
  intro D hD hsub
  have hsub' : D ⊆ Metric.ball x (m : ℝ) := hsub.trans (Metric.ball_subset_ball hm)
  have hle := ContinuousPath.exitTime_mono hsub' b
  have hfin : ContinuousPath.exitTime D b < ∞ := lt_of_le_of_lt hle (hball m)
  have heq : (lbmExitTime F D b).toReal = F b (ContinuousPath.exitTime D b).toNNReal := by
    rw [lbmExitTime_eq_clockValue hD hf (ne_of_lt hfin)]
    have hnneg : 0 ≤ F b (ContinuousPath.exitTime D b).toNNReal := by
      simpa only [hf.map_zero] using hf.strictMono.monotone
        (show (0 : ℝ≥0) ≤ (ContinuousPath.exitTime D b).toNNReal from bot_le)
    simp [hnneg]
  rw [heq]
  exact hn _ (ENNReal.toNNReal_mono (ne_of_lt (hball m)) hle)

end HarmonicBalls
