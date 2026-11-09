import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQGMetric

/-!
# First-pass frozen input for Lemmas 11.15 and 11.16 (fp-S11j, owner n4)

FIRST-PASS FROZEN input (EXTERNAL; truth check pending). A `def ... : Prop`, never an axiom.

Cameron-Martin transfer for the LQG metric event of the first pinch event (paper `lemma:first-event-proof`,
corrected paper lines 3659-3696, and Step 15.4 of notes/fp-gaps/CHATGPT-11-15-17-faithful.md): the shifted
field `h + f` for a smooth compactly supported `f` vanishing on the unit circle has a law mutually absolutely
continuous with that of the whole-plane GFF `h`, and the metric of `h + f` is the Weyl scaling `e^{ξ f} D_h`.
Hence a metric event of positive probability for `h + f` has positive probability for `h`.

Source: Miller-Sheffield, Imaginary Geometry IV, arXiv:1302.4738v2, Proposition 2.9 (printed p. 49), for the
Cameron-Martin equivalence; Weyl scaling of the LQG metric under the field shift (Dubedat-Falconet-Gwynne-Pfeffer-Sun,
arXiv:1905.00380v2, Axiom III, and Proposition 3.17 at the insertion). The same Cameron-Martin pattern as
`CameronMartinEventTransferFrozen` (FirstPass/Frozen/S11c.lean:150), specialised to a single metric event.
-/

universe u

namespace HarmonicBalls

open MeasureTheory


/-- FIRST-PASS FROZEN (EXTERNAL; FALSE AS WRITTEN, truth check 2026-11-09, `notes/fp-gaps/CHATGPT-CM-metric-truth.md`
section 1: the predicate `B` is not required to be measurable). Superseded by
`CameronMartinMetricEventTransferMeasurableFrozen` below; kept unchanged, not used by the assembly.

Cameron-Martin transfer of a metric event under a smooth shift. For `0 < γ < 2`,
`α₀ < Q_γ`, a smooth compactly supported `f` vanishing on the unit circle, and a predicate `B` on metrics: if the event
that the Weyl-shifted metric `e^{ξ f} D_h` lies in `B` has positive probability, and both events are null-measurable,
then the event that `D_h` lies in `B` has positive probability. -/
def CameronMartinMetricEventTransferFrozen : Prop :=
  ∀ (γ α₀ ξ : ℝ) (f : ℂ → ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → (∀ z : ℂ, ‖z‖ = 1 → f z = 0) →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (B : (ℂ → ℂ → ℝ) → Prop),
  IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α₀ hC D →
  NullMeasurableSet {ω | B (fun x y => (weylScaling (D ω) ξ f x y).toReal)} P →
  NullMeasurableSet {ω | B (D ω)} P →
  0 < P {ω | B (fun x y => (weylScaling (D ω) ξ f x y).toReal)} → 0 < P {ω | B (D ω)}

/-- RETIRED (operator 22:44 UTC): superseded by `cameronMartinFieldCertificateTransfer` (proved, FirstPass/S11j/
CertificateTransfer.lean); not used by any proof; kept, never deleted.

FIRST-PASS FROZEN (EXTERNAL, proposed minimal correction of `CameronMartinMetricEventTransferFrozen`, truth check
`notes/fp-gaps/CHATGPT-CM-metric-truth.md` section 1: add the measurability of the predicate `B` in the product
σ-algebra on metrics; the Cameron-Martin absolute continuity `Law(e^{ξ f} D_h) ≪ Law(D_h)` gives the stated direction).
Acceptance is the operator's (ACCEPT check) and is pending. Same content as the superseded predicate, plus
`MeasurableSet {d | B d}`. -/
def CameronMartinMetricEventTransferMeasurableFrozen : Prop :=
  ∀ (γ α₀ ξ : ℝ) (f : ℂ → ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → (∀ z : ℂ, ‖z‖ = 1 → f z = 0) →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (B : (ℂ → ℂ → ℝ) → Prop),
  MeasurableSet {d : ℂ → ℂ → ℝ | B d} →
  IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α₀ hC D →
  NullMeasurableSet {ω | B (fun x y => (weylScaling (D ω) ξ f x y).toReal)} P →
  NullMeasurableSet {ω | B (D ω)} P →
  0 < P {ω | B (fun x y => (weylScaling (D ω) ξ f x y).toReal)} → 0 < P {ω | B (D ω)}

/-- FIRST-PASS FROZEN (EXTERNAL; truth check pending; operator ruling Q1, 23:12 UTC). Metric-level Weyl composition
(not to be confused with the field-level `WeylScalingCompositionFrozen` of `Frozen/S11d.lean`):
scaling a metric `D` by `g` and then by `f` is scaling it by `g + f`, for an exponent `ξ > 0`, an Euclidean length
metric `D`, weights `f, g` continuous on `ℂ \ {0}` (the log singularity `-α₀ log|·|` is continuous there), and finite
inner scaling. Here `weylScaling D ξ g` is the infimum over `D`-length parametrized paths of `∫ e^{ξ g(P t)} dt`
(`Defs/LQGMetric.lean`), and the inner metric enters only through `toReal`.

Source: Bou-Rabee-Gwynne (arXiv:2208.11795) Fact 2.2 III, corrected paper line 445, which defines `e^{ξ f} · D` as this
infimum; GM21 = Gwynne-Miller, (1.8), p. 6. The composition is the weighted-length identity: the `D'`-length of a
`D`-parametrized path is `∫ e^{ξ g} dℓ_D`, and the change of parameter `dσ = e^{ξ g} dr` gives the weight `g + f`.
Used by the common-field identification of the shifted metric (`FirstPass/S11j/FieldLevel11_15.lean`). -/
def WeylMetricCompositionFrozen : Prop :=
  ∀ ξ : ℝ, 0 < ξ → ∀ (D : ℂ → ℂ → ℝ) (g f : ℂ → ℝ), IsEuclideanLengthMetric D →
    ContinuousOn g {z | z ≠ 0} → ContinuousOn f {z | z ≠ 0} →
    (∀ x y, weylScaling D ξ g x y ≠ ⊤) →
    ∀ x y, weylScaling (fun u v => (weylScaling D ξ g u v).toReal) ξ f x y =
      weylScaling D ξ (fun z => g z + f z) x y

/-- FIRST-PASS FROZEN (EXTERNAL; truth check pending; operator note 22:53 UTC, item B(a)). The Weyl exponent of an LQG
metric is positive: `ξ = γ / d_γ` (Ding-Gwynne, arXiv:2108.12060, Theorem 1.9; the argument of
`notes/fp-gaps/CHATGPT-xi-exponent-rigidity.md` section 3). Stated for `0 < γ < 2`, the only range used. -/
def LQGMetricExponentPositive : Prop :=
  ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 → 0 < ξ

end HarmonicBalls
