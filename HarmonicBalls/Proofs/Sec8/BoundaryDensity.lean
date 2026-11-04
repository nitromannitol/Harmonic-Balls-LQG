import HarmonicBalls.Proofs.Sec8.GoodScaleBoundary
import HarmonicBalls.Proofs.Sec8.OpenBallDensity

/-!
# Boundary measure from good scales and Harnack exclusion

Combines Besicovitch density with the deterministic good-scale reduction in
the proof of Proposition 8.1. The probabilistic prevalence and the Harnack
estimate remain explicit hypotheses.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- An open set has null boundary if almost every boundary point has many
comparable very good scales and those scales satisfy Harnack exclusion. -/
theorem measure_frontier_eq_zero_of_good_scales_and_harnack
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] {s : Set ℂ} (hs : IsOpen s)
    (βminus : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m α ζ : ℝ)
    (hm : 0 < m) (hα : 0 < α) (hζ : ζ < 1)
    (hcount : ∀ᵐ z ∂μ.restrict (frontier s), ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤
        veryGoodComparableScaleCount μ βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N)
    (hexclude : ∀ᵐ z ∂μ.restrict (frontier s), ∀ᶠ n : ℕ in atTop,
      IsVeryGoodAnnulus μ βminus (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ →
      μ (s ∩ annulus z (dyadicScale (n + 1)) (dyadicScale n)) ≤
        ENNReal.ofReal α * μ (annulus z (dyadicScale (n + 1)) (dyadicScale n)) →
      s ∩ ball z (dyadicScale n / 2) = ∅) :
    μ (frontier s) = 0 := by
  apply ae_restrict_eq_bot.1
  apply Filter.eventually_false_iff_eq_bot.1
  filter_upwards [hcount, ae_eventually_measure_inter_dyadicBall_le_on_frontier μ hs α m hα hm,
    hexclude, ae_restrict_mem isClosed_frontier.measurableSet]
    with z hzcount hzdensity hzexclude hzfront
  obtain ⟨K₁, hK₁⟩ := Filter.eventually_atTop.1 hzdensity
  obtain ⟨K₂, hK₂⟩ := Filter.eventually_atTop.1 hzexclude
  obtain ⟨n, hn, hv, hc⟩ :=
    exists_veryGoodComparableScale_ge_of_count μ βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ
      hζ hzcount (max K₁ K₂)
  have hmass := measure_inter_annulus_le_of_ball_comparison μ s z n α m hc
    (hK₁ n (le_trans (le_max_left _ _) hn))
  have hdisjoint := hK₂ n (le_trans (le_max_right _ _) hn) hv hmass
  exact not_mem_closure_of_disjoint_ball (half_pos (dyadicScale_pos n)) hdisjoint
    (frontier_subset_closure hzfront)

end HarmonicBalls
