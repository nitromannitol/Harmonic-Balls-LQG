import HarmonicBalls.FirstPass.Closure.Main12Canonical
import HarmonicBalls.FirstPass.Closure.Bridge12Canonical
import HarmonicBalls.FirstPass.S11i.Faithful

/-!
# Theorem 1.2 at the canonical exponent, fed by the numbered Lemma 11.13 (fp-counted-1-2-of-11-13, z3)

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

end HarmonicBalls.Closure
