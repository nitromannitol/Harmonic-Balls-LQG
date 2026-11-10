import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Proposed.LQG

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

/-- RETIRED (FALSE as written; operator note 23:37 UTC, ChatGPT truth check `notes/fp-gaps/CHATGPT-n4-frozen-truth-weyl.md`
section 1: the outer weight `f` is only required to be continuous on `ℂ ∖ {0}`, and a weight singular at `0` lets a path
of infinite `D`-length become essential). Not used by any proof after the 23:37 UTC note; kept, never deleted. Superseded
by `WeylMetricCompositionContinuousOuterFrozen` below.

FIRST-PASS FROZEN (EXTERNAL; truth check pending; operator ruling Q1, 23:12 UTC). Metric-level Weyl composition
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

/-- FIRST-PASS FROZEN (EXTERNAL; truth check pending; operator notes 22:53 UTC item B(a) and 23:37 UTC). The Weyl exponent
of an LQG metric is positive: `ξ > 0` for `IsLQGMetric γ ξ 𝔇`, `0 < γ < 2`, the only range used. The statement is TRUE.
Its source is the positivity argument, not Ding-Gwynne Theorem 1.9 (which assumes `ξ > 0`): normalized whole-plane GFF
scaling, constant Weyl scaling, coordinate change and the Euclidean topology (Bou-Rabee-Gwynne arXiv:2208.11795, Section
2.1, (2.1)-(2.2), p. 8); see `notes/fp-gaps/CHATGPT-xi-exponent-rigidity.md` section 3. -/
def LQGMetricExponentPositive : Prop :=
  ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 → 0 < ξ

/-- FIRST-PASS FROZEN (EXTERNAL; truth check TRUE (ChatGPT, 00:28 UTC); operator note 23:37 UTC, replacing the retired
`WeylMetricCompositionFrozen`). Metric-level Weyl composition with a CONTINUOUS outer shift: for `ξ > 0`, an Euclidean
length metric `D`, a weight `g` continuous on `ℂ ∖ {0}` (the log singularity is continuous there) with finite inner
scaling, and a continuous weight `f`, scaling by `g` and then by `f` is scaling by `g + f`. Here `weylScaling D ξ g` is
the infimum of `∫ e^{ξ g}` over `D`-length parametrized paths (`Defs/LQGMetric.lean`), the inner metric enters via `toReal`.
Source: Bou-Rabee-Gwynne (arXiv:2208.11795) Fact 2.2 III, corrected paper line 445; GM21 = Gwynne-Miller, (1.8), p. 6.
The correction `ContinuousOn f {z | z ≠ 0}` ↦ `Continuous f` is the one of `notes/fp-gaps/CHATGPT-n4-frozen-truth-weyl.md`
("Minimal Lean fix"), which gives a deterministic proof of the corrected statement. Proof idea (path approximation): for the exact
finite-length definition, approximate by finite-length paths (notes/fp-gaps/CHATGPT-hb-frozen-truth-0026.md, section 1). -/
def WeylMetricCompositionContinuousOuterFrozen : Prop :=
  ∀ ξ : ℝ, 0 < ξ → ∀ (D : ℂ → ℂ → ℝ) (g f : ℂ → ℝ), IsEuclideanLengthMetric D →
    ContinuousOn g {z | z ≠ 0} → Continuous f →
    (∀ x y, weylScaling D ξ g x y ≠ ⊤) →
    ∀ x y, weylScaling (fun u v => (weylScaling D ξ g u v).toReal) ξ f x y =
      weylScaling D ξ (fun z => g z + f z) x y

/-- FIRST-PASS FROZEN (EXTERNAL; truth check TRUE (ChatGPT, 00:28 UTC); operator ruling B1, 23:42 UTC, option (a): a universe-`u`
restatement of the axiom clause used). For `0 < γ < 2`, every γ-LQG metric `𝔇` (`IsLQGMetric γ ξ 𝔇`) and every
whole-plane GFF `h^ℂ` on a probability space `Ω : Type u`, the metric `𝔇(h^ℂ)` is almost surely a Euclidean length metric
(`IsEuclideanLengthMetric`, axiom I of Fact 2.2 at `h^ℂ`, with no insertion). Source: the axioms of `IsLQGMetric`
(`Defs/LQGMetric.lean`, `satisfiesLQGMetricAxioms` at `f = 0`), which quantify over `Ω : Type`; the universe lift holds
because the axioms involve only the joint law of the field and the metric (`IsLQGMetric` docstring); GM21 Theorem 1.2 (p. 6);
Gwynne-Miller 2021, Fact 2.2 I (paper lines 432-453).
Proof idea (universe reduction): reduce the large probability space to a small space of observations, apply the original
clause at `f = 0`, and pull back (notes/fp-gaps/CHATGPT-hb-frozen-truth-0026.md, section 2). -/
def LQGMetricLengthUnivFrozen : Prop :=
  ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω))

/-- FIRST-PASS FROZEN (PROPOSED input `LQGMetricFieldAxioms`, `Proposed/LQG.lean:199`, pending operator source-check;
universal form). Truth check TRUE (ChatGPT, 00:28 UTC): the universe wrapper preserves the proposed statement; its content
includes the singular-insertion theorem and the free-`ξ` reduction (notes/fp-gaps/CHATGPT-hb-frozen-truth-0026.md, section 3). The Fact 2.2 axioms I-IV for the field `h^ℂ - α₀ log|·|` hold on every probability space `Ω : Type u`,
for all `γ`, `ξ`, `α₀`, every whole-plane GFF `hC`, and all `P`. Used only as the hypothesis `haxioms` of
`firstPass_11_15_corrected` (`FirstPass/S11j/FieldAssembly11_15.lean`). -/
def LQGMetricFieldAxiomsUnivFrozen : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc

end HarmonicBalls
