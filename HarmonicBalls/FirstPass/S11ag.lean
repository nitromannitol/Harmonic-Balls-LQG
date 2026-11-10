import HarmonicBalls.FirstPass.S11ab

/-! # Metric-and-measure event certificate for the second local event (fp-S11ag)

The pair version of `MetricEventCertificateStmt` (`FirstPass/S11ab.lean`): the event is a predicate `Φ` of the metric `D`
and of the insertion-`α` LQG measure `μ` of the same whole-plane GFF. It is the form that the Cameron-Martin transfer of the
second local event `E₂ = {a₁ > d₁, μ(U) > M S}` (`pinchSecondEventLocal`, `FirstPass/S11h/LocalEvents.lean`) needs (z3,
blocker B2). The statement is a named form that the decoded rule must supply; it is not an External or Proposed input.
-/

namespace HarmonicBalls.S11ag

open MeasureTheory Set Metric

universe u

/-- Named form, pair (metric and measure) version of the decoded rule: for every insertion `α < Q` and every whole-plane
GFF model with insertion metric `D` (`IsLQGMetricOfField`) and insertion-`α` LQG measure `μ` (`IsLQGMeasureOfField`), there is
a `distributionMeasurableSpace`-measurable set `B` of distributions such that, almost surely, the field lies in `B` iff the
pair `(D ω, μ ω)` satisfies `Φ`. Not an External or Proposed Prop; a form the rule must supply. -/
def MetricMeasureEventCertificateStmt (γ ξ : ℝ) (Φ : (ℂ → ℂ → ℝ) → Measure ℂ → Prop) : Prop :=
  ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α hC D → IsLQGMeasureOfField P γ α hcirc μ →
    ∃ B : Set ((ℂ → ℝ) → ℝ), MeasurableSet[distributionMeasurableSpace] B ∧
      ∀ᵐ ω ∂P, hC ω ∈ B ↔ Φ (D ω) (μ ω)

end HarmonicBalls.S11ag
