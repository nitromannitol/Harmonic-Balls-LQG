import HarmonicBalls.FirstPass.S11.MetricBall
import HarmonicBalls.Proposed.MetricProperness

/-!
# Compactness from large-scale metric crossings

The deterministic conclusion of the proof of Dubédat, Falconet, Gwynne,
Pfeffer and Sun, Lemma 3.8: sufficiently large crossings force metric balls
to lie in bounded Euclidean sets.
-/

namespace HarmonicBalls

/-- Large metric distances across arbitrarily large annuli imply compactness
of all closed metric balls in the Euclidean topology. -/
theorem IsEuclideanLengthMetric.isCompact_closedBall_of_far_crossing
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hfar : ∀ N R : ℝ, ∃ ρ : ℝ, R ≤ ρ ∧ ∀ x y : ℂ,
      ‖x‖ ≤ ρ → 3 / 2 * ρ ≤ ‖y‖ → N ≤ D x y)
    (z : ℂ) (R : ℝ) : IsCompact {w : ℂ | D z w ≤ R} := by
  obtain ⟨ρ, hz, hρ⟩ := hfar (R + 1) ‖z‖
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (FirstPassS11.continuous_dist_right hD z) continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 3 / 2 * ρ)).subset ?_
  intro w hw
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hn
  push Not at hn
  have h := hρ z w hz hn.le
  change D z w ≤ R at hw
  linarith

end HarmonicBalls
