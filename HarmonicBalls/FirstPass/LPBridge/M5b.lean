import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Defs.Notation
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.LPStage.GFF
import HarmonicBalls.LPStage.LQGMeasure
import HarmonicBalls.LPStage.LengthMetric
import HarmonicBalls.LPStage.LQGMetric
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M5a

/-!
# Bridge to the staged random half of the γ-LQG metric (module M5b)

For each of the four staged definitions of `HarmonicBalls/LPStage/LQGMetric.lean` there is a bridge between the HB
definition (`HarmonicBalls.*`, Defs/LQGMetric.lean, and `HarmonicBalls.LQGMetricFieldAxioms`, Proposed/LQG.lean) and its
LP copy (`LatticeProb.LQG.*`). The HB definitions are kept, and no counted statement is changed.

None of the four bridges is `rfl`: each definition is a structure, an existential, or an implication-valued Prop over
distinct types. Each equivalence is built field by field from:
* the `rfl` bridges of M1 (`distributionMeasurableSpace_eq`, `pairingSigmaAlgebra_eq`, `addFunPairing_eq`,
  `affinePullbackPairing_eq`, `fieldSigmaAlgebra_eq`) and of M5a (`internalMetric_eq`, `weylScaling_eq`), which make the
  fields agree by definitional unfolding;
* the equivalences `isWholePlaneGFF_iff` (M1) and `isEuclideanLengthMetric_iff` (M5a), which transport the hypotheses and
  the length-metric conjuncts.

`LQGMetricFieldAxioms` is a literature input (Proposed). The bridge `lqgMetricFieldAxioms_iff` relates the two copies of
the Prop; it does not assert it.
-/

namespace HarmonicBalls.LPBridge

open MeasureTheory Set
open scoped ENNReal NNReal

/-- Axioms I-IV for a random generalized function: the HB structure `SatisfiesLQGMetricAxioms` and its LP copy have
equivalent fields (the length-metric field by `isEuclideanLengthMetric_iff`; the others by definitional unfolding). -/
theorem satisfiesLQGMetricAxioms_iff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ : ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h : Ω → (ℂ → ℝ) → ℝ) :
    HarmonicBalls.SatisfiesLQGMetricAxioms P γ ξ 𝔇 h ↔
      LatticeProb.LQG.SatisfiesLQGMetricAxioms P γ ξ 𝔇 h where
  mp H :=
    { ae_isEuclideanLengthMetric :=
        H.ae_isEuclideanLengthMetric.mono fun _ hω => (isEuclideanLengthMetric_iff _).mp hω
      locality := H.locality
      ae_weylScaling := H.ae_weylScaling
      coordChange := H.coordChange }
  mpr H :=
    { ae_isEuclideanLengthMetric :=
        H.ae_isEuclideanLengthMetric.mono fun _ hω => (isEuclideanLengthMetric_iff _).mpr hω
      locality := H.locality
      ae_weylScaling := H.ae_weylScaling
      coordChange := H.coordChange }

/-- The γ-LQG metric property `IsLQGMetric γ ξ 𝔇` is equivalent to its LP copy: the measurability field is defeq, and
the field of axioms over every whole-plane GFF plus a random continuous function is transported by
`isWholePlaneGFF_iff` and `satisfiesLQGMetricAxioms_iff`. -/
theorem isLQGMetric_iff (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) :
    HarmonicBalls.IsLQGMetric γ ξ 𝔇 ↔ LatticeProb.LQG.IsLQGMetric γ ξ 𝔇 := by
  constructor
  · intro H
    refine ⟨H.measurable_apply, ?_⟩
    intro Ω _ P hC hcirc f hW hc hm
    exact (satisfiesLQGMetricAxioms_iff P γ ξ 𝔇 _).mp
      (H.satisfiesLQGMetricAxioms Ω P hC hcirc f ((isWholePlaneGFF_iff P hC hcirc).mpr hW) hc hm)
  · intro H
    refine ⟨H.measurable_apply, ?_⟩
    intro Ω _ P hC hcirc f hW hc hm
    exact (satisfiesLQGMetricAxioms_iff P γ ξ 𝔇 _).mpr
      (H.satisfiesLQGMetricAxioms Ω P hC hcirc f ((isWholePlaneGFF_iff P hC hcirc).mp hW) hc hm)

/-- The γ-LQG metric of the logarithmically shifted field, `IsLQGMetricOfField`, is equivalent to its LP copy: an
existential over a γ-LQG metric `𝔇` (`isLQGMetric_iff`) with the same almost-sure Weyl-scaling identity (the Weyl scaling
is rfl-bridged by `weylScaling_eq`). -/
theorem isLQGMetricOfField_iff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (D : Ω → ℂ → ℂ → ℝ) :
    HarmonicBalls.IsLQGMetricOfField P γ ξ α₀ hC D ↔ LatticeProb.LQG.IsLQGMetricOfField P γ ξ α₀ hC D := by
  unfold HarmonicBalls.IsLQGMetricOfField LatticeProb.LQG.IsLQGMetricOfField
  constructor
  · rintro ⟨𝔇, h1, h2⟩
    exact ⟨𝔇, (isLQGMetric_iff γ ξ 𝔇).mp h1, h2⟩
  · rintro ⟨𝔇, h1, h2⟩
    exact ⟨𝔇, (isLQGMetric_iff γ ξ 𝔇).mpr h1, h2⟩

/-- **Literature input, bridged as an equivalence of the two copies of the Prop; not a theorem.** The HB statement
`HarmonicBalls.LQGMetricFieldAxioms` (Proposed/LQG.lean) and its LP copy `LatticeProb.LQG.LQGMetricFieldAxioms` are
equivalent. Each hypothesis and conclusion is transported by `isWholePlaneGFF_iff`, `isLQGMetric_iff`,
`isEuclideanLengthMetric_iff` and the rfl bridges; the literature content is not asserted here. -/
theorem lqgMetricFieldAxioms_iff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    HarmonicBalls.LQGMetricFieldAxioms P γ ξ α₀ hC hcirc ↔
      LatticeProb.LQG.LQGMetricFieldAxioms P γ ξ α₀ hC hcirc := by
  unfold HarmonicBalls.LQGMetricFieldAxioms LatticeProb.LQG.LQGMetricFieldAxioms
  constructor
  · intro H hW h0 h1 h2 𝔇 hM
    obtain ⟨I, II, III, IV⟩ :=
      H ((isWholePlaneGFF_iff P hC hcirc).mpr hW) h0 h1 h2 𝔇 ((isLQGMetric_iff γ ξ 𝔇).mpr hM)
    refine ⟨?_, II, III, IV⟩
    exact I.mono fun _ hω => ⟨hω.1, (isEuclideanLengthMetric_iff _).mp hω.2⟩
  · intro H hW h0 h1 h2 𝔇 hM
    obtain ⟨I, II, III, IV⟩ :=
      H ((isWholePlaneGFF_iff P hC hcirc).mp hW) h0 h1 h2 𝔇 ((isLQGMetric_iff γ ξ 𝔇).mp hM)
    refine ⟨?_, II, III, IV⟩
    exact I.mono fun _ hω => ⟨hω.1, (isEuclideanLengthMetric_iff _).mpr hω.2⟩

end HarmonicBalls.LPBridge
