import HarmonicBalls.FirstPass.Closure
import HarmonicBalls.FirstPass.Closure.SecA45
import HarmonicBalls.FirstPass.Closure.Sec78910
import HarmonicBalls.FirstPass.Closure.PaperExponentOf13
import HarmonicBalls.FirstPass.S8dNoWeyl
import HarmonicBalls.FirstPass.S8c.BirkhoffDerived
import HarmonicBalls.FirstPass.S8c.WeylOffOriginDerived

/-!
# Phase 2: counted results 1.x to 10.x without the frozen inputs `BirkhoffPointwiseErgodic` and
`LocalLQGInsertionWeylOffOrigin`

For each counted declaration of a numbered result 1.x to 10.x (`docs/campaign/PHASE2-INVENTORY.md`, section 1)
whose signature takes the frozen Prop `BirkhoffPointwiseErgodic` or `LocalLQGInsertionWeylOffOrigin` as a binder,
this file states `<countedName>_derivedInputs`: the same statement with those binders removed, proved by applying
the counted declaration to the derived theorems `birkhoffPointwiseErgodic_derived`
(`FirstPass/S8c/BirkhoffDerived.lean`) and `localLQGInsertionWeylOffOrigin_derived`
(`FirstPass/S8c/WeylOffOriginDerived.lean`). The other binders, and the proofs of the counted declarations, are
unchanged. No existing file is edited (task fp-phase2-derived-inputs-s1-10, worker z3).
Results 1.x to 10.x that take neither input have no wrapper here.
-/

namespace HarmonicBalls.Closure

universe u

/-- Result 1.1 (`closure_1_1`, HarmonicBalls/FirstPass/Closure.lean:154) without the frozen inputs
    `hWeyl`, `hB`: `closure_1_1` applied to the derived theorems
    `localLQGInsertionWeylOffOrigin_derived` (FirstPass/S8c/WeylOffOriginDerived.lean:88);
    `birkhoffPointwiseErgodic_derived` (FirstPass/S8c/BirkhoffDerived.lean:21). Same statement
    as `closure_1_1` minus those binders (no hypothesis is added or weakened). -/
theorem closure_1_1_derivedInputs
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    : ExistenceUniquenessHarmonicBallsStmt.{u} :=
    HarmonicBalls.Closure.closure_1_1.{u} hL1
      HarmonicBalls.localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3
      HarmonicBalls.birkhoffPointwiseErgodic_derived.{0} hDG hAff hCC hW hE hN

/-- Result 1.3 (`closure_1_3`, HarmonicBalls/FirstPass/Closure.lean:221) without the frozen inputs
    `hWeyl`, `hB`: `closure_1_3` applied to the derived theorems
    `localLQGInsertionWeylOffOrigin_derived` (FirstPass/S8c/WeylOffOriginDerived.lean:88);
    `birkhoffPointwiseErgodic_derived` (FirstPass/S8c/BirkhoffDerived.lean:21). Same statement
    as `closure_1_3` minus those binders (no hypothesis is added or weakened). -/
theorem closure_1_3_derivedInputs
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureLocality P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    : HarmonicBallLocalSetStmt.{u} :=
    HarmonicBalls.Closure.closure_1_3.{u} hmeasure hL1
      HarmonicBalls.localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3
      HarmonicBalls.birkhoffPointwiseErgodic_derived.{0} hDG hAff hCC hW hE hN

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure

open MeasureTheory Metric Set Filter Topology

universe u

/-- Result 1.2 (`closure_1_2_paperExponent_of_11_13`,
    HarmonicBalls/FirstPass/Closure/PaperExponentOf13.lean:54) without the frozen input `hB`:
    `closure_1_2_paperExponent_of_11_13` applied to the derived theorem
    `birkhoffPointwiseErgodic_derived` (FirstPass/S8c/BirkhoffDerived.lean:21). Same statement
    as `closure_1_2_paperExponent_of_11_13` minus those binders (no hypothesis is added or
    weakened). -/
theorem closure_1_2_paperExponent_of_11_13_derivedInputs
    (_hDim : WholePlaneLQGGraphDimension)
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (h13 : CorrectedLemma11_13CanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    : HarmonicBallNoveltyFaithfulStmt.{u} :=
    HarmonicBalls.Closure.closure_1_2_paperExponent_of_11_13.{u} _hDim hDG hAff hCC hW hE hN hL1 hE1
      hE3 HarmonicBalls.birkhoffPointwiseErgodic_derived.{0} hCamp hDecFrozen hDec hCM hAx h13 hTor

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure

open MeasureTheory

universe u

/-- Result 5.2 (`closure_5_2`, HarmonicBalls/FirstPass/Closure/SecA45.lean:163) without the frozen
    inputs `hWeyl`, `hB`: `closure_5_2` applied to the derived theorems
    `localLQGInsertionWeylOffOrigin_derived` (FirstPass/S8c/WeylOffOriginDerived.lean:88);
    `birkhoffPointwiseErgodic_derived` (FirstPass/S8c/BirkhoffDerived.lean:21). Same statement
    as `closure_5_2` minus those binders (no hypothesis is added or weakened). -/
theorem closure_5_2_derivedInputs
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : ClusterContinuityStmt.{u} :=
    HarmonicBalls.Closure.closure_5_2.{u} hDG hCC hE hW hN hL1
      HarmonicBalls.localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3
      HarmonicBalls.birkhoffPointwiseErgodic_derived.{0}

/-- Result 5.3 (`closure_5_3`, HarmonicBalls/FirstPass/Closure/SecA45.lean:182) without the frozen
    inputs `hWeyl`, `hB`: `closure_5_3` applied to the derived theorems
    `localLQGInsertionWeylOffOrigin_derived` (FirstPass/S8c/WeylOffOriginDerived.lean:88);
    `birkhoffPointwiseErgodic_derived` (FirstPass/S8c/BirkhoffDerived.lean:21). Same statement
    as `closure_5_3` minus those binders (no hypothesis is added or weakened). -/
theorem closure_5_3_derivedInputs
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : ClusterBoundaryMeasureZeroStmt.{u} :=
    HarmonicBalls.Closure.closure_5_3.{u} hDG hCC hE hW hN hL1
      HarmonicBalls.localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3
      HarmonicBalls.birkhoffPointwiseErgodic_derived.{0}

/-- Result 5.4 (`closure_5_4`, HarmonicBalls/FirstPass/Closure/SecA45.lean:201) without the frozen
    inputs `hWeyl`, `hB`: `closure_5_4` applied to the derived theorems
    `localLQGInsertionWeylOffOrigin_derived` (FirstPass/S8c/WeylOffOriginDerived.lean:88);
    `birkhoffPointwiseErgodic_derived` (FirstPass/S8c/BirkhoffDerived.lean:21). Same statement
    as `closure_5_4` minus those binders (no hypothesis is added or weakened). -/
theorem closure_5_4_derivedInputs
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : RegularizedClusterHarmonicBallsStmt.{u} :=
    HarmonicBalls.Closure.closure_5_4.{u} hDG hCC hE hW hN hL1
      HarmonicBalls.localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3
      HarmonicBalls.birkhoffPointwiseErgodic_derived.{0}

/-- Result 5.5 (`closure_5_5`, HarmonicBalls/FirstPass/Closure/SecA45.lean:220) without the frozen
    inputs `hWeyl`, `hB`: `closure_5_5` applied to the derived theorems
    `localLQGInsertionWeylOffOrigin_derived` (FirstPass/S8c/WeylOffOriginDerived.lean:88);
    `birkhoffPointwiseErgodic_derived` (FirstPass/S8c/BirkhoffDerived.lean:21). Same statement
    as `closure_5_5` minus those binders (no hypothesis is added or weakened). -/
theorem closure_5_5_derivedInputs
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : ExistenceHarmonicBallsStmt.{u} :=
    HarmonicBalls.Closure.closure_5_5.{u} hDG hCC hE hW hN hL1
      HarmonicBalls.localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3
      HarmonicBalls.birkhoffPointwiseErgodic_derived.{0}

/-- Result 7.2 (`closure_7_2`, HarmonicBalls/FirstPass/Closure/Sec78910.lean:100) without the frozen
    inputs `hWeyl`, `hB`: `closure_7_2` applied to the derived theorems
    `localLQGInsertionWeylOffOrigin_derived` (FirstPass/S8c/WeylOffOriginDerived.lean:88);
    `birkhoffPointwiseErgodic_derived` (FirstPass/S8c/BirkhoffDerived.lean:21). Same statement
    as `closure_7_2` minus those binders (no hypothesis is added or weakened). -/
theorem closure_7_2_derivedInputs
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    : ClusterTimeContinuityStmt.{u} :=
    HarmonicBalls.Closure.closure_7_2.{u} hL1
      HarmonicBalls.localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3
      HarmonicBalls.birkhoffPointwiseErgodic_derived.{0} hDG hAff hCC hW hE hN

/-- Result 8.1 (`closure_8_1`, HarmonicBalls/FirstPass/Closure/Sec78910.lean:126) without the frozen
    inputs `hWeyl`, `hB`: `closure_8_1` applied to the derived theorems
    `localLQGInsertionWeylOffOrigin_derived` (FirstPass/S8c/WeylOffOriginDerived.lean:88);
    `birkhoffPointwiseErgodic_derived` (FirstPass/S8c/BirkhoffDerived.lean:21). Same statement
    as `closure_8_1` minus those binders (no hypothesis is added or weakened). -/
theorem closure_8_1_derivedInputs
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    : BoundaryMeasureZeroOfCompactClusterStmt.{u} :=
    HarmonicBalls.Closure.closure_8_1.{u} hL1
      HarmonicBalls.localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3
      HarmonicBalls.birkhoffPointwiseErgodic_derived.{0} hDG hAff hCC hW hE hN

/-- Result 9.2 (`closure_9_2`, HarmonicBalls/FirstPass/Closure/Sec78910.lean:170) without the frozen
    inputs `hWeyl`, `hB`: `closure_9_2` applied to the derived theorems
    `localLQGInsertionWeylOffOrigin_derived` (FirstPass/S8c/WeylOffOriginDerived.lean:88);
    `birkhoffPointwiseErgodic_derived` (FirstPass/S8c/BirkhoffDerived.lean:21). Same statement
    as `closure_9_2` minus those binders (no hypothesis is added or weakened). -/
theorem closure_9_2_derivedInputs
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    : HarmonicBalls.S9c.SubharmonicBallUniquenessC51Stmt.{u} :=
    HarmonicBalls.Closure.closure_9_2.{u} hL1
      HarmonicBalls.localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3
      HarmonicBalls.birkhoffPointwiseErgodic_derived.{0} hDG hAff hCC hW hE hN

/-- Result 10.7 (`closure_10_7`, HarmonicBalls/FirstPass/Closure/Sec78910.lean:289) without the
    frozen inputs `hWeyl`, `hB`: `closure_10_7` applied to the derived theorems
    `localLQGInsertionWeylOffOrigin_derived` (FirstPass/S8c/WeylOffOriginDerived.lean:88);
    `birkhoffPointwiseErgodic_derived` (FirstPass/S8c/BirkhoffDerived.lean:21). Same statement
    as `closure_10_7` minus those binders (no hypothesis is added or weakened). -/
theorem closure_10_7_derivedInputs
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hTor : TorhorstSimpleLoopFrozen)
    : HarmonicBallComplementBoundaryJordanStmt.{u} :=
    HarmonicBalls.Closure.closure_10_7.{u} hL1
      HarmonicBalls.localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3
      HarmonicBalls.birkhoffPointwiseErgodic_derived.{0} hDG hAff hCC hW hE hN hTor

end HarmonicBalls.Closure

namespace HarmonicBalls

open MeasureTheory

universe u

/-- Result 8.2 (`firstPass_8_2_S8d_noWeyl`, HarmonicBalls/FirstPass/S8dNoWeyl.lean:26) without the
    frozen input `hB`: `firstPass_8_2_S8d_noWeyl` applied to the derived theorem
    `birkhoffPointwiseErgodic_derived` (FirstPass/S8c/BirkhoffDerived.lean:21). Same statement
    as `firstPass_8_2_S8d_noWeyl` minus those binders (no hypothesis is added or weakened). -/
theorem firstPass_8_2_S8d_noWeyl_derivedInputs
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hfull : LQGMeasureFullSupportStmt.{u})
    (hL67 : VeryGoodAnnulusProbabilityStmt.{u})
    (hEx : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : TypicalPointManyGoodScalesStmt.{u} :=
    HarmonicBalls.firstPass_8_2_S8d_noWeyl.{u} hL1 hfull hL67 hEx hN hAff hCC hE1 hE3
      HarmonicBalls.birkhoffPointwiseErgodic_derived.{0}

end HarmonicBalls

