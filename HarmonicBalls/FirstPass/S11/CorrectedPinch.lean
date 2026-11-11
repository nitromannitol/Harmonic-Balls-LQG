import HarmonicBalls.Draft.Section11
import HarmonicBalls.Draft.Section6

/-!
# Corrected statement of Lemma 11.12 (pinch positivity for every exponent)

The Draft statement `PinchEventPositiveProbabilityStmt` (`Draft/Section11.lean:246`) is the uncorrected case `α₀ = 0`.
The corrected form (paper `lemma:mu_h-pinch-positive-probability`, line 3239) replaces it by
the local-certificate assertion for `Ĝ_1` and every `α < Q`, with the event in the field σ-algebra on `B_7` modulo
additive constants. Lemma 11.13 (`ManyPinchScalesStmt`) needs this general-`α` form (the rooted application uses
`α = γ`), so the corrected form is the statement that the first-pass theorem for Lemma 11.12 must prove.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- Lemma 11.12, corrected form (paper line 3239, correction [C43]). For the fixed buffered pinch-point configuration:
for every `α < Q = lqgQ γ`, every whole-plane GFF `P` with LQG measure `μ` at exponent `α` and LQG metric `D` at
exponents `(γ, ξ, α)`, and every `M > 0`, there is an event `E` of the field σ-algebra on `B_7` modulo additive
constants (`Section6.fieldSigmaAlgebraModConst α hC (ball 0 7)`) with `0 < P E`, on which the pinch event
`Ĝ_1^{h^α}(0; M)` holds.

GAP NOTE (not encoded): the paper also asks that E^α(M) be defined by a rule independent of α (paper line 3240).
This statement only asks for the existence of such an E for each α, so it is weaker than the printed corrected lemma
in that respect.
-/
def PinchEventPositiveCorrectedStmt : Prop :=
  ∃ U T Q' Q : Set ℂ, IsPinchPointConfiguration U T Q' Q ∧
  ∀ γ ξ α : ℝ, 0 < γ → γ < 2 → α < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α hcirc μ → IsLQGMetricOfField P γ ξ α hC D →
  ∀ M : ℝ, 0 < M →
    ∃ E : Set Ω, MeasurableSet[Section6.fieldSigmaAlgebraModConst α hC (ball 0 7)] E ∧ 0 < P E ∧
      E ⊆ {ω | pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0}

end HarmonicBalls
