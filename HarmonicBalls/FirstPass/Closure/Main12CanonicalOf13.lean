import HarmonicBalls.FirstPass.Closure.Main12Canonical
import HarmonicBalls.FirstPass.Closure.Bridge12Canonical
import HarmonicBalls.FirstPass.S11i.Faithful
import HarmonicBalls.FirstPass.S11v.Affine

/-!
# Theorem 1.2 at the canonical exponent, fed by the numbered Lemma 11.13

File `HarmonicBalls/FirstPass/Closure/Main12CanonicalOf13.lean`, namespace `HarmonicBalls.Closure`.

The counted canonical closures of Theorem 1.2 take the numbered canonical Lemma 11.13 itself,
`h13 : CorrectedLemma11_13CanonicalStmt` (`FirstPass/S11i/Faithful.lean:102`). It is passed through
`manyPinchScalesCanonicalModel_of_canonical` (`Closure/Bridge12Canonical.lean:54`) to the model-dependent density of
`ManyPinchScalesCanonicalModelStmt` (`Closure/Bridge12Canonical.lean:42`), which `firstPassMain_1_2_canonical`
(`Closure/Main12Canonical.lean:33`) takes as `h13`. The closures `closure_1_2_canonical` and
`closure_1_2_faithful_canonical` (`Closure/Main12Canonical.lean`), which take the internal part (d) `hId` instead, are unchanged.

Binders: those of `closure_1_2_canonical` (`Closure/Main12Canonical.lean:96`), with the inputs of `closure_11_13_canonical`
(`Closure/Sec11.lean:400`) and `hId` replaced by `h13`. Dropped, as unused after the replacement: `hLen`, `hN2`, `hμW`,
`hCanon`, `hNonat`, `hExists`, `hfr`, `hmass`, `hCMAbs`, `hCMRew`, `hComp`, `hMf`, `hDiam`, `hMk`, `hholder`, `hShift`,
`hFD`, `hDC`, `hCMT`, `hPos10`, `hMassM`, `hSupM`, `hFin`, `hWIC`, `hM1`, `hM2`, `hId`. Kept: `hDG hAff hCC hW hE hN hL1 hE1
hE3 hB hCamp hDecFrozen hDec hCM hAx`, then `h13` and `hTor`. No new hypothesis and no new mathematics.
-/

universe u

namespace HarmonicBalls.Closure

/-- **Closure of Theorem 1.2 at the canonical exponent, fed by the numbered Lemma 11.13** (`HarmonicBallNoveltyCanonicalStmt`).
Proof: `firstPassMain_1_2_canonical` with `h13` passed through `manyPinchScalesCanonicalModel_of_canonical`; otherwise as
`closure_1_2_canonical`. -/
theorem closure_1_2_canonical_of_11_13
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
    (h13 : CorrectedLemma11_13CanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallNoveltyCanonicalStmt.{u} :=
  firstPassMain_1_2_canonical hDG hAff hCC hW hE hN (volumeGrowthI2_of_staged hDG hCC hW hE hN)
    (closure_8_2 hL1 localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3 hB hDG hAff hCC hW hE hN)
    (closure_11_7 hDG hCamp hDecFrozen hDec hCM
      (fun γ α₀ Ω _ P hC hcirc => hCC Ω P γ α₀ hC hcirc)
      (fun γ α₀ Ω _ P hC hcirc => hE Ω P γ α₀ hC hcirc)
      (fun γ α₀ Ω _ P hC hcirc => hN Ω P γ α₀ hC hcirc))
    (manyPinchScalesCanonicalModel_of_canonical h13)
    hTor
    (fun γ α₀ ξ _ _ _ Ω _ P hC hcirc _ => hAx Ω P γ ξ α₀ hC hcirc)

/-- **Closure of the faithful Theorem 1.2 at the canonical exponent, fed by the numbered Lemma 11.13**
(`HarmonicBallNoveltyFaithfulStmt`): the hypotheses of `closure_1_2_canonical_of_11_13`, with the conclusion restricted by
`harmonicBallNoveltyFaithful_of_canonical` (`Closure/Main12Canonical.lean:169`). Mirror of
`closure_1_2_faithful_canonical` (`Closure/Main12Canonical.lean:182`). -/
theorem closure_1_2_faithful_canonical_of_11_13
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
    (h13 : CorrectedLemma11_13CanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallNoveltyFaithfulStmt.{u} :=
  harmonicBallNoveltyFaithful_of_canonical.{u}
    (closure_1_2_canonical_of_11_13 hDG hAff hCC hW hE hN hL1 hE1 hE3 hB hCamp hDecFrozen hDec hCM hAx h13 hTor)

/-- **Counted form of the faithful Theorem 1.2** (superseded by `firstPass_1_2_faithful`, which drops the external
`hAff` and the duplicate `hDecFrozen`; kept unchanged) (`theorem:harmonic-balls-properties`, arbitrary carrier `Ω : Type u`, and radii restricted to `0 < s` as in `HarmonicBallNoveltyFaithfulStmt`). The conclusion is
`HarmonicBallNoveltyFaithfulStmt`, the faithful statement with the positive-radius condition, at the canonical exponent
`ξ = γ / lqgGraphDimension γ`; it is not the unrestricted `HarmonicBallNoveltyCanonicalStmt`. Same binders and conclusion as
`closure_1_2_faithful_canonical_of_11_13` (`FirstPass/Closure/Main12CanonicalOf13.lean:70`), proved by applying it.
`hE1` and `hDecFrozen` are two occurrences of the same external proposition `LQGMeasureOfProfileMeasurableFrozen`;
`hAx` is a universal-ξ external interface (harmless). -/
theorem firstPass_1_2_faithful_v1
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
    (h13 : CorrectedLemma11_13CanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallNoveltyFaithfulStmt.{u} :=
  closure_1_2_faithful_canonical_of_11_13 hDG hAff hCC hW hE hN hL1 hE1 hE3 hB hCamp hDecFrozen hDec hCM hAx h13 hTor

/-- **Closure of Theorem 1.2 at the canonical exponent, fed by the numbered Lemma 11.13**

The binders of `closure_1_2_canonical_of_11_13` with two changes:
the external `hAff` is removed, and its two uses are discharged by `HarmonicBalls.wholePlaneGFFAffineInvariance_derived`
(`FirstPass/S11v/Affine.lean:145`, derived from `IsWholePlaneGFF` alone); the duplicate `hDecFrozen` is removed, and `hE1`
is passed to `closure_11_7` in its place (both have the type `LQGMeasureOfProfileMeasurableFrozen.{u}`). The local root
kernel input `hL1` is unchanged (its helper body is checked by `localRootKernel_ac_ae`, `FirstPass/Closure/LocalRootKernelAc.lean`).
Conclusion `HarmonicBallNoveltyCanonicalStmt`. -/
theorem closure_1_2_canonical_of_11_13_clean
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
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
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (h13 : CorrectedLemma11_13CanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallNoveltyCanonicalStmt.{u} := by
  have hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc :=
    fun _ _ P hC hcirc => HarmonicBalls.wholePlaneGFFAffineInvariance_derived P hC hcirc
  exact firstPassMain_1_2_canonical hDG hAff hCC hW hE hN (volumeGrowthI2_of_staged hDG hCC hW hE hN)
    (closure_8_2 hL1 localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3 hB hDG hAff hCC hW hE hN)
    (closure_11_7 hDG hCamp hE1 hDec hCM
      (fun γ α₀ Ω _ P hC hcirc => hCC Ω P γ α₀ hC hcirc)
      (fun γ α₀ Ω _ P hC hcirc => hE Ω P γ α₀ hC hcirc)
      (fun γ α₀ Ω _ P hC hcirc => hN Ω P γ α₀ hC hcirc))
    (manyPinchScalesCanonicalModel_of_canonical h13)
    hTor
    (fun γ α₀ ξ _ _ _ Ω _ P hC hcirc _ => hAx Ω P γ ξ α₀ hC hcirc)

/-- **Closure of the faithful Theorem 1.2 at the canonical exponent**: the binders of `closure_1_2_canonical_of_11_13_clean`, with the conclusion restricted to the positive radii by
`harmonicBallNoveltyFaithful_of_canonical` (`Closure/Main12Canonical.lean:169`). Mirror of `closure_1_2_faithful_canonical_of_11_13`
(v1, with `hAff` and `hDecFrozen`). -/
theorem closure_1_2_faithful_canonical_of_11_13_clean
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
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
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (h13 : CorrectedLemma11_13CanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallNoveltyFaithfulStmt.{u} :=
  harmonicBallNoveltyFaithful_of_canonical.{u}
    (closure_1_2_canonical_of_11_13_clean hDG hCC hW hE hN hL1 hE1 hE3 hB hCamp hDec hCM hAx h13 hTor)

/-- **Counted form of the faithful Theorem 1.2** (`theorem:harmonic-balls-properties`, arbitrary carrier `Ω : Type u`, radii restricted to `0 < s` as in `HarmonicBallNoveltyFaithfulStmt`), with no external `hAff` and no duplicate `hDecFrozen`. Conclusion
`HarmonicBallNoveltyFaithfulStmt` at `ξ = γ / lqgGraphDimension γ`. Proof: `closure_1_2_faithful_canonical_of_11_13_clean`.
`hE1` is the single occurrence of `LQGMeasureOfProfileMeasurableFrozen`; `hAx` is a universal-ξ external interface
(harmless). The earlier binder list is kept as `firstPass_1_2_faithful_v1`. -/
theorem firstPass_1_2_faithful
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
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
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (h13 : CorrectedLemma11_13CanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallNoveltyFaithfulStmt.{u} :=
  closure_1_2_faithful_canonical_of_11_13_clean hDG hCC hW hE hN hL1 hE1 hE3 hB hCamp hDec hCM hAx h13 hTor

end HarmonicBalls.Closure
