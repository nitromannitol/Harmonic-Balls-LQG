import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Proposed.LQG

/-!
# First-pass frozen input for Lemma 11.12 (fp-S11m, owner z4)

FIRST-PASS FROZEN inputs (EXTERNAL; truth check pending). A `def ... : Prop`, never an axiom.

Only the Euclidean length property of the Weyl-shifted LQG metric by a smooth compactly supported weight is frozen
here (operator note 01:41 UTC, item 2). The other inputs of the local certificate are reused from the frozen files:
`LQGMetricFieldAxiomsUnivFrozen` (`FirstPass/Frozen/S11j.lean`) for the length property of the α-metric itself, and
`CameronMartinMetricEventTransferMeasurableFrozen` (`FirstPass/Frozen/S11j.lean`) for the Cameron-Martin transfer.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- FIRST-PASS FROZEN (EXTERNAL; truth check pending; operator note 01:41 UTC, item 2). For `0 < γ < 2`, `α < Q_γ`,
every γ-LQG metric `𝔇` with Weyl exponent `ξ` (`IsLQGMetric γ ξ 𝔇`) and every whole-plane GFF `h^ℂ` on a probability
space `Ω : Type u`, and every smooth compactly supported `f : ℂ → ℝ`, almost surely the metric `e^{ξ f} D_h` is a
Euclidean length metric, where `D_h = weylScaling (𝔇 (h^ℂ)) ξ (-α log |·|)` is the α-metric (`IsLQGMetricOfField`).
Equivalently, the α-metric of the shifted field `h^ℂ + f` is a Euclidean length metric (GM21 axiom I for the field
`h^ℂ + f - α log |·|`, with the Weyl scaling of axiom III, eq. (1.8)). Source: Gwynne-Miller, arXiv:1905.00383v3, Section
1.2, p. 6 (Fact 2.2 I, paper lines 432-453); Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, p. 9 (Weyl scaling by
`-α log|·|`). Used by: `firstPass_11_12_corrected` through `pinchFirstEventLocal_weylScaling` (argument `hE`). -/
def LQGMetricAlphaWeylShiftLengthFrozen : Prop :=
  ∀ (γ ξ α : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → α < lqgQ γ → IsLQGMetric γ ξ 𝔇 →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → ∀ f : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y =>
      (weylScaling (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal) ξ f x y).toReal)

end HarmonicBalls
