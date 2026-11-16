import HarmonicBalls.Proofs.Potential.BrownianSharpStoppedBallOccupation

/-! # Sharp occupation up to bounded-domain exit

A single almost-sure event gives the sharp logarithmic ball occupation bound
up to exit from every bounded domain. The constants may depend on the path and
the domain.
-/

open MeasureTheory MarkovProcess Set
open scoped ENNReal

namespace HarmonicBalls

/-- For each starting point, one almost-sure event works for every bounded set.
The positive constant and radius threshold may depend on the path and set, and
are uniform over ball centers and sufficiently small radii. -/
theorem planarBrownianMotion_stopped_uniform_ball_occupation_log_all_domains (x : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ D : Set ℂ, Bornology.IsBounded D →
      ∃ C : ℝ, 0 < C ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
        ∀ (z : ℂ) (r : ℝ), 0 < r → r < r₀ →
          stoppedBrownianOccupation D b (Metric.ball z r) ≤
            ENNReal.ofReal (C * r ^ 2 * (Real.log (1 / r)) ^ 2) := by
  have hballs : ∀ᵐ b ∂(planarBrownianMotion x), ∀ n : ℕ,
      ContinuousPath.exitTime (Metric.ball x (n : ℝ)) b < ∞ := by
    simp only [ae_all_iff]
    exact fun n => Section6.ae_planarBrownianMotion_exitTime_ball_lt_top x n
  filter_upwards [planarBrownianMotion_uniform_ball_occupation_log_all_horizons x,
    hballs] with b hb hball D hD
  obtain ⟨R, hR⟩ := hD.subset_ball x
  obtain ⟨n, hn⟩ := exists_nat_ge R
  have hsub : D ⊆ Metric.ball x (n : ℝ) :=
    hR.trans (Metric.ball_subset_ball hn)
  have hfin : ContinuousPath.exitTime D b < ∞ :=
    lt_of_le_of_lt (ContinuousPath.exitTime_mono hsub b) (hball n)
  obtain ⟨C, hC, r₀, hr₀, hbound⟩ :=
    hb (ContinuousPath.exitTime D b).toReal ENNReal.toReal_nonneg
  refine ⟨C, hC, r₀, hr₀, fun z r hr hrsmall => ?_⟩
  exact (stoppedBrownianOccupation_ball_le D b hfin.ne z r).trans (hbound z r hr hrsmall)

end HarmonicBalls
