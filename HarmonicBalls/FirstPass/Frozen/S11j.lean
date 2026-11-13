import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Proposed.LQG

/-!
# Frozen input for Lemmas 11.15 and 11.16

FROZEN input (EXTERNAL; truth check pending). A `def ... : Prop`, never an axiom.

Cameron-Martin transfer for the LQG metric event of the first pinch event (paper `lemma:first-event-proof`, corrected paper lines 3659-3696): the shifted
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


/-- RETIRED: superseded by `cameronMartinFieldCertificateTransfer` (proved, FirstPass/S11j/
CertificateTransfer.lean); not used by any proof; kept, never deleted.

FROZEN (EXTERNAL). Cameron-Martin transfer of a metric event under a smooth shift. For `0 < γ < 2`,
`α₀ < Q_γ`, a smooth compactly supported `f` vanishing on the unit circle, and a predicate `B` on metrics, measurable for
the product σ-algebra on metrics: if the event that the Weyl-shifted metric `e^{ξ f} D_h` lies in `B` has positive
probability, and both events are null-measurable, then the event that `D_h` lies in `B` has positive probability. The
Cameron-Martin absolute continuity `Law(e^{ξ f} D_h) ≪ Law(D_h)` gives this direction. Source: Miller-Sheffield
arXiv:1302.4738v2, Proposition 2.9, p. 49, equation (2.8), proof p. 50. Acceptance is pending. -/
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

/-- FROZEN (EXTERNAL; truth check TRUE). The Weyl exponent
of an LQG metric is positive: `ξ > 0` for `IsLQGMetric γ ξ 𝔇`, `0 < γ < 2`, the only range used. The statement is TRUE.
Its source is the positivity argument, not Ding-Gwynne Theorem 1.9 (which assumes `ξ > 0`): normalized whole-plane GFF
scaling, constant Weyl scaling, coordinate change and the Euclidean topology (Bou-Rabee-Gwynne arXiv:2208.11795, Section
2.1, (2.1)-(2.2), p. 8). The same argument prints the normalized
metric-scaling identity as Gwynne-Miller (1.15), p. 11.
derived: lqgMetricExponentPositive_of_inputs (FirstPass/S11x.lean) -/
def LQGMetricExponentPositive : Prop :=
  ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 → 0 < ξ

/-- FROZEN (EXTERNAL, truth check TRUE). Metric-level Weyl composition with a CONTINUOUS outer shift: for `ξ > 0`, an Euclidean
length metric `D`, a weight `g` continuous on `ℂ ∖ {0}` (the log singularity is continuous there) with finite inner
scaling, and a continuous weight `f`, scaling by `g` and then by `f` is scaling by `g + f`. Here `weylScaling D ξ g` is
the infimum of `∫ e^{ξ g}` over `D`-length parametrized paths (`Defs/LQGMetric.lean`), the inner metric enters via `toReal`.
Source: Bou-Rabee-Gwynne (arXiv:2208.11795) Fact 2.2 III, corrected paper line 445; GM21 = Gwynne-Miller, (1.8), p. 6.
The correction `ContinuousOn f {z | z ≠ 0}` ↦ `Continuous f` is the one that gives a deterministic proof of the corrected statement. Proof idea (path approximation): for the exact
finite-length definition, approximate by finite-length paths (section 1). -/
def WeylMetricCompositionContinuousOuterFrozen : Prop :=
  ∀ ξ : ℝ, 0 < ξ → ∀ (D : ℂ → ℂ → ℝ) (g f : ℂ → ℝ), IsEuclideanLengthMetric D →
    ContinuousOn g {z | z ≠ 0} → Continuous f →
    (∀ x y, weylScaling D ξ g x y ≠ ⊤) →
    ∀ x y, weylScaling (fun u v => (weylScaling D ξ g u v).toReal) ξ f x y =
      weylScaling D ξ (fun z => g z + f z) x y

/-- FROZEN (EXTERNAL; truth check TRUE; a universe-`u`
restatement of the axiom clause used). For `0 < γ < 2`, every γ-LQG metric `𝔇` (`IsLQGMetric γ ξ 𝔇`) and every
whole-plane GFF `h^ℂ` on a probability space `Ω : Type u`, the metric `𝔇(h^ℂ)` is almost surely a Euclidean length metric
(`IsEuclideanLengthMetric`, axiom I of Fact 2.2 at `h^ℂ`, with no insertion). Source: the axioms of `IsLQGMetric`
(`Defs/LQGMetric.lean`, `satisfiesLQGMetricAxioms` at `f = 0`), which quantify over `Ω : Type`; the universe lift holds
because the axioms involve only the joint law of the field and the metric (`IsLQGMetric` docstring); GM21 Theorem 1.2 (p. 6);
Gwynne-Miller 2021, Fact 2.2 I (paper lines 432-453).
Proof idea (universe reduction): reduce the large probability space to a small space of observations, apply the original
clause at `f = 0`, and pull back (section 2). -/
def LQGMetricLengthUnivFrozen : Prop :=
  ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω))

/-- FROZEN (PROPOSED input `LQGMetricFieldAxioms`, `Proposed/LQG.lean:201` (docstring l.183-200), PENDING source-check for the universal wrapper;
universal form). Truth check TRUE: the universe wrapper preserves the proposed statement; its content
includes the singular-insertion theorem and the free-`ξ` reduction (section 3). The Fact 2.2 axioms I-IV for the field `h^ℂ - α₀ log|·|` hold on every probability space `Ω : Type u`,
for all `γ`, `ξ`, `α₀`, every whole-plane GFF `hC`, and all `P`.
Published sources (copied from the docstring of `LQGMetricFieldAxioms`, `Proposed/LQG.lean:183-200`): Bou-Rabee-Gwynne
arXiv:2208.11795, Fact 2.2 (paper lines 432-453; verification remark at line 455); Gwynne-Miller arXiv:1905.00383, Section 1.2
(p. 6), Remark 1.5 (p. 8); Dubédat-Falconet-Gwynne-Pfeffer-Sun arXiv:1905.00380, definition p. 9, Theorem 1.10 (p. 10; finiteness
for `α₀ < Q`), Proposition 3.17 (p. 43; Euclidean topology).
Published sources (section 3): HB Fact 2.2, printed p. 10; DFGPS
arXiv:1905.00380v2, Theorem 1.10 (p. 10) and Proposition 3.17 (p. 43); Ding-Gwynne arXiv:2108.12060, Theorem 1.9 (p. 7; background
charge `Q(ξ) = Q_γ`); Gwynne-Pfeffer arXiv:1903.09561v3, equation (4.2) and Lemma 4.1 (p. 10; `ξ = γ/d_γ` in the subcritical range).
Caveat on `ξ` (`Proposed/LQG.lean:183-200`): the Prop quantifies over every `ξ` for which `IsLQGMetric` holds; the literature
constructs γ-LQG metrics only for `ξ = γ/d_γ`.
Counted consumers: `firstPass_11_12_final` (`FirstPass/S11m/Final11_12.lean:131`), `firstPass_11_15_corrected`
(`FirstPass/S11j/FieldAssembly11_15.lean:276`), `firstPass_11_16_corrected` (`FirstPass/S11k/FirstLExterior.lean:260`),
`firstPass_11_17_corrected` (`FirstPass/S11h/PinchCertificateProof11_17.lean:294`). Not used by `firstPass_11_13_corrected`
(`FirstPass/S11i/Corrected11_13.lean:65`). Thirty-one further files in `HarmonicBalls` mention it (`grep -rln`). -/
def LQGMetricFieldAxiomsUnivFrozen : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc

end HarmonicBalls
