import HarmonicBalls.Defs.LQGMetric

/-!
# Bounded compactness of the whole-plane LQG metric

This is a staged literature input, pending operator source-check. It is stated
only for the normalized whole-plane GFF. In particular, it does not assert
properness for a field with a logarithmic singularity.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter

universe u

/-- **Whole-plane LQG metric bounded compactness.** Dubédat, Falconet,
Gwynne, Pfeffer and Sun, *Weak LQG metrics and Liouville first passage
percolation*, Probability Theory and Related Fields 178 (2020), Lemma 3.8,
p. 408: almost surely every closed bounded subset of the whole-plane LQG
metric is compact. In the Euclidean topology induced by the metric, this is
expressed by compactness of every closed metric ball.

The exponent `ξ` is restricted through the explicit `IsLQGMetric γ ξ 𝔇`
hypothesis, as in the existing metric-field propositions. -/
def WholePlaneLQGMetricBoundedlyCompact
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 →
  ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
    ∀ᵐ ω ∂P, ∀ z : ℂ, ∀ R : ℝ,
      IsCompact {w : ℂ | 𝔇 (hC ω) z w ≤ R}

end HarmonicBalls
