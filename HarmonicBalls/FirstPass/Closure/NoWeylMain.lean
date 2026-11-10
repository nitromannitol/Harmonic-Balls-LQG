import HarmonicBalls.FirstPass.Closure
import HarmonicBalls.FirstPass.Closure.Faithful12
import HarmonicBalls.FirstPass.Closure.Sec78910
import HarmonicBalls.FirstPass.S8c.WeylOffOriginDerived

/-! # Closures of the first pass without the Weyl binder (FIRST-PASS fp-closure-noWeyl-main, worker z6)

`LocalLQGInsertionWeylOffOrigin` (`hWeyl`, `FirstPass/Frozen/S8c.lean`) is derived, with no hypotheses, by
`localLQGInsertionWeylOffOrigin_derived` (`FirstPass/S8c/WeylOffOriginDerived.lean`). Each `<name>_noWeyl` below is the
closure `<name>` with the binder `hWeyl` removed, the argument `hWeyl` being replaced by `localLQGInsertionWeylOffOrigin_derived`.
The originals are unchanged. Covered: Theorems 1.1, 1.2, 1.3 (`closure_1_1`, `closure_1_2`, `closure_1_3`), the faithful
Theorem 1.2 (`closure_1_2_faithful`), Lemmas 7.2, 8.1, 9.2 and Proposition 10.7 (`closure_7_2`, `closure_8_1`, `closure_9_2`,
`closure_10_7`). The Section 11 closures are in `FirstPass/Closure/Sec11NoWeyl.lean`. -/

namespace HarmonicBalls.Closure

open MeasureTheory

universe u

/-- `closure_1_1_noWeyl`: the closure `closure_1_1` (Theorem 1.1) without the binder `hWeyl : LocalLQGInsertionWeylOffOrigin`.
The Weyl relation off the origin is supplied by `localLQGInsertionWeylOffOrigin_derived`
(`FirstPass/S8c/WeylOffOriginDerived.lean`). The statement is that of `closure_1_1` minus the binder; the original is unchanged. -/
theorem closure_1_1_noWeyl
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
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
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    ExistenceUniquenessHarmonicBallsStmt.{u} :=
  firstPassMain_1_1 hDG hCC hE (closure_8_2 hL1 localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3 hB hDG hAff hCC hW hE hN)

/-- `closure_1_2_noWeyl`: the closure `closure_1_2` (Theorem 1.2) without the binder `hWeyl : LocalLQGInsertionWeylOffOrigin`.
The Weyl relation off the origin is supplied by `localLQGInsertionWeylOffOrigin_derived`
(`FirstPass/S8c/WeylOffOriginDerived.lean`). The statement is that of `closure_1_2` minus the binder; the original is unchanged. -/
theorem closure_1_2_noWeyl
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
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hStep8 : Step8IdentificationStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallNoveltyStmt.{u} :=
  firstPassMain_1_2 hDG hAff hCC hW hE hN (volumeGrowthI2_of_staged hDG hCC hW hE hN)
    (closure_8_2 hL1 localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3 hB hDG hAff hCC hW hE hN)
    (closure_11_7 hDG hCamp hDecFrozen hDec hCM
      (fun γ α₀ Ω _ P hC hcirc => hCC Ω P γ α₀ hC hcirc)
      (fun γ α₀ Ω _ P hC hcirc => hE Ω P γ α₀ hC hcirc)
      (fun γ α₀ Ω _ P hC hcirc => hN Ω P γ α₀ hC hcirc))
    (manyPinchScales_of_corrected (closure_11_13 hAx hE hStep8))
    hTor
    (fun γ α₀ ξ _ _ _ Ω _ P hC hcirc _ => hAx Ω P γ ξ α₀ hC hcirc)

/-- `closure_1_3_noWeyl`: the closure `closure_1_3` (Theorem 1.3) without the binder `hWeyl : LocalLQGInsertionWeylOffOrigin`.
The Weyl relation off the origin is supplied by `localLQGInsertionWeylOffOrigin_derived`
(`FirstPass/S8c/WeylOffOriginDerived.lean`). The statement is that of `closure_1_3` minus the binder; the original is unchanged. -/
theorem closure_1_3_noWeyl
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureLocality P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
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
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    HarmonicBallLocalSetStmt.{u} :=
  firstPassMain_1_3 (volumeGrowthI2_of_staged hDG hCC hW hE hN) hDG hCC hE
    (closure_8_2 hL1 localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3 hB hDG hAff hCC hW hE hN) hmeasure

/-- `closure_1_2_faithful_noWeyl`: the closure `closure_1_2_faithful` (Theorem 1.2 (faithful form)) without the binder `hWeyl : LocalLQGInsertionWeylOffOrigin`.
The Weyl relation off the origin is supplied by `localLQGInsertionWeylOffOrigin_derived`
(`FirstPass/S8c/WeylOffOriginDerived.lean`). The statement is that of `closure_1_2_faithful` minus the binder; the original is unchanged. -/
theorem closure_1_2_faithful_noWeyl
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
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hStep8 : Step8IdentificationStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallNoveltyFaithfulStmt.{u} :=
  harmonicBallNoveltyFaithful_of_stmt.{u}
    (closure_1_2 hDG hAff hCC hW hE hN hL1 localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3 hB hCamp hDecFrozen hDec hCM hAx hStep8 hTor)

/-- `closure_7_2_noWeyl`: the closure `closure_7_2` (Lemma 7.2) without the binder `hWeyl : LocalLQGInsertionWeylOffOrigin`.
The Weyl relation off the origin is supplied by `localLQGInsertionWeylOffOrigin_derived`
(`FirstPass/S8c/WeylOffOriginDerived.lean`). The statement is that of `closure_7_2` minus the binder; the original is unchanged. -/
theorem closure_7_2_noWeyl
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
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
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    ClusterTimeContinuityStmt.{u} :=
  HarmonicBalls.firstPass_7_2 hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE
    (closure_8_2 hL1 localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3 hB hDG hAff hCC hW hE hN)

/-- `closure_8_1_noWeyl`: the closure `closure_8_1` (Lemma 8.1) without the binder `hWeyl : LocalLQGInsertionWeylOffOrigin`.
The Weyl relation off the origin is supplied by `localLQGInsertionWeylOffOrigin_derived`
(`FirstPass/S8c/WeylOffOriginDerived.lean`). The statement is that of `closure_8_1` minus the binder; the original is unchanged. -/
theorem closure_8_1_noWeyl
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
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
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    BoundaryMeasureZeroOfCompactClusterStmt.{u} :=
  HarmonicBalls.firstPass_8_1 hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE
    (closure_8_2 hL1 localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3 hB hDG hAff hCC hW hE hN)

/-- `closure_9_2_noWeyl`: the closure `closure_9_2` (Lemma 9.2) without the binder `hWeyl : LocalLQGInsertionWeylOffOrigin`.
The Weyl relation off the origin is supplied by `localLQGInsertionWeylOffOrigin_derived`
(`FirstPass/S8c/WeylOffOriginDerived.lean`). The statement is that of `closure_9_2` minus the binder; the original is unchanged. -/
theorem closure_9_2_noWeyl
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
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
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    HarmonicBalls.S9c.SubharmonicBallUniquenessC51Stmt.{u} :=
  HarmonicBalls.S9c.firstPass_9_2_corrected hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hW
    (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc) hN
    (closure_8_2 hL1 localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3 hB hDG hAff hCC hW hE hN)

/-- `closure_10_7_noWeyl`: the closure `closure_10_7` (Proposition 10.7) without the binder `hWeyl : LocalLQGInsertionWeylOffOrigin`.
The Weyl relation off the origin is supplied by `localLQGInsertionWeylOffOrigin_derived`
(`FirstPass/S8c/WeylOffOriginDerived.lean`). The statement is that of `closure_10_7` minus the binder; the original is unchanged. -/
theorem closure_10_7_noWeyl
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
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
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallComplementBoundaryJordanStmt.{u} :=
  HarmonicBalls.firstPass_10_7
    (HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_five_staged_inputs hDG
      (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hW (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc) hN)
    (HarmonicBalls.firstPass_5_5 hDG (fun {Ω} _ P γ α₀ hC hcirc => hCC Ω P γ α₀ hC hcirc) hE
      (closure_8_2 hL1 localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3 hB hDG hAff hCC hW hE hN))
    (closure_10_6 hDG hAff hCC hW hE hN hTor) hAff hCC

end HarmonicBalls.Closure
