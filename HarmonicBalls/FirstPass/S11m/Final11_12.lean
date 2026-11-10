import HarmonicBalls.FirstPass.S11m.CertificateAssembly
import HarmonicBalls.FirstPass.S11t
import HarmonicBalls.FirstPass.S11x
import HarmonicBalls.Steps.Sec2.VolumeGrowth
import HarmonicBalls.Proofs.Sec2.SingularAtomAtZero
import HarmonicBalls.FirstPass.S11v.Affine

/-!
# Lemma 11.12 (corrected): final assembly from named inputs (fp-S11m-11-12-faithful, owner z4)

`firstPass_11_12_of_inputs` proves `CorrectedLemma11_12Stmt` (`FirstPass/S11i/Faithful.lean:56`) from named
hypotheses only. Three hypotheses of `firstPass_11_12_corrected_of_inputs` are derived results, discharged here by
repository proofs:

* `hBase` (`LQGMetricBaseComparisonStmt`) by `S11ak.lqgMetricBaseComparison_of_canonical`
  (`FirstPass/S11ak/BaseComparison.lean:67`), from `hCanon`, `hLen`, `hEx`;
* `hS` (`BundleParts.PinchSecondAnnulusStep`, the N2 step, OPEN in `FirstPass/S11k/BundleParts.lean:41`) by
  `PinchSecondAnnulusS11t.pinchSecondAnnulusStep_of_N2_inputs` (`FirstPass/S11t.lean:30`), from `hMf`, `hholder`,
  `hEx`, `hμW` (at `α₀ = 0`), `hNonat` (at `α₀ = 0` and `α₀`);
* `hXi` (`LQGMetricExponentPositive`, `FirstPass/Frozen/S11j.lean:105`) by `lqgMetricExponentPositive_of_inputs`
  (`FirstPass/S11x.lean:94`), from `hExists` and `hAff`.

The remaining named hypotheses, with their class:

* FIRST-PASS FROZEN (`Frozen/` files unless stated): `hAx` `LQGMetricFieldAxiomsUnivFrozen` (`Frozen/S11j.lean:143`);
  `hLen` `LQGMetricLengthUnivFrozen` (`Frozen/S11j.lean:133`); `hLoc` `LocalLQGDecoderCommonFrozen`
  (`Frozen/S11c.lean:386`); `hCanon` `LQGCanonicalDecodersExistStmt` (`Frozen/S11n.lean:30`); `hExists`
  `WholePlaneGFFExistsFrozen` (`S11r/Frozen.lean:37`); `hfr` `LQGInternalMetricWeylAeMeasurableFrozen`
  (`Frozen/S11d.lean:123`); `hmass` `LQGMassFunctionalMeasurableFrozen` (`Frozen/S11d.lean:144`); `hCMAbs`
  `CameronMartinGFFMutualAbsCont` (`Frozen/S11d.lean:74`); `hCMRew` `CameronMartinGFFReweighting`
  (`Frozen/S11aj.lean:31`); `hComp` `WeylScalingCompositionFrozen` (`Frozen/S11d.lean:89`); `hMf`
  `LQGMassInnerMeasurableFrozen` (`Frozen/S11k.lean:58`); `hDiam` `LQGInternalDiamInnerMeasurableFrozen`
  (`Frozen/S11k.lean:74`); `hMk` `DomainMarkovConditionalPositiveFrozen` (`Frozen/S11k.lean:43`).
* PROPOSED, universal forms, PENDING operator source-check: `hμW` `LQGMeasureWeylScaling` (`Proposed/LQG.lean:95`);
  `hNonat` `LQGMeasureNonatomicAll` (`S11n/MeasureDecoder.lean:34`, of `Proposed/LQG.lean:77`); `hEx`
  `LQGMeasureExistence` at `α₀ = 0` (`Proposed/LQG.lean:68`); `hAff` `WholePlaneGFFAffineInvariance`
  (`Proposed/LQG.lean:53`).
* CITED DRAFT statements of numbered results: `hDsm` `SmallMetricDiameterLargeMassStmt` (Proposition 11.9,
  `Draft/Section11.lean:201`); `hholder` `GreenPotentialHolderStmt` (Proposition 2.5, `Draft/Section2.lean:190`).
* NOT YET CLASSIFIED (reported): `hN2` `LocalMetricReplacementStmt` (n2, `S11r/LocalMetricReplacement.lean:53`, kept
  as an input by the operator's 04:48 UTC note, not in a `Frozen/` file); `hgrowth` `LQGVolumeGrowthAllScalesStmt`
  (`Draft/Section2.lean:122`, I2), whose docstring describes it as a consequence of Lemma 2.4 (paper line 501), not a
  numbered result. Its derivation `lqgVolumeGrowthAllScalesStmt_of_ballMass` (`Steps/Sec2/VolumeGrowth.lean:164`) needs
  `LiouvilleBallMassBoundStep` (`Steps/Sec2/VolumeGrowth.lean:69`), which restates Lemma 2.4 and is unproved.
  `LQGMeasureFullSupportStmt` (I1, `Draft/Section2.lean:109`) is discharged from `hgrowth` by
  `lqgMeasureFullSupportStmt_of_volumeGrowth` (`Steps/Sec2/VolumeGrowth.lean:220`).
-/

namespace HarmonicBalls.S11m.Final11_12

open MeasureTheory Set Metric Filter
open scoped ENNReal

universe u

/-- **Lemma 11.12 (corrected), `CorrectedLemma11_12Stmt`, from named inputs only.** The hypotheses are listed in the
module docstring; the derived ones (`hBase`, `hS`, `hXi`, `hFull`) are discharged in the proof, and the rest are the hypotheses
of `firstPass_11_12_corrected_of_inputs` (`FirstPass/S11m/CertificateAssembly.lean`). -/
theorem firstPass_11_12_of_inputs
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hLen : LQGMetricLengthUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hμW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u})
    (hEx : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hAff : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hmass : LQGMassFunctionalMeasurableFrozen.{u})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{u})
    (hCMRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hDsm : SmallMetricDiameterLargeMassStmt.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u}) :
    CorrectedLemma11_12Stmt.{u} := by
  have hXi : LQGMetricExponentPositive := lqgMetricExponentPositive_of_inputs hExists hAff
  have hFull : LQGMeasureFullSupportStmt.{u} := HarmonicBalls.lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth
  have hBase : HarmonicBalls.S11ak.LQGMetricBaseComparisonStmt.{u} :=
    HarmonicBalls.S11ak.lqgMetricBaseComparison_of_canonical hCanon hLen hEx
  have hS : BundleParts.PinchSecondAnnulusStep.{u} :=
    HarmonicBalls.PinchSecondAnnulusS11t.pinchSecondAnnulusStep_of_N2_inputs hMf hholder hEx
      (fun γ Ω _ P hC hcirc => hμW Ω P γ 0 hC hcirc)
      (fun γ Ω _ P hC hcirc => hNonat γ 0 Ω P hC hcirc)
      (fun γ α₀ Ω _ P hC hcirc => hNonat γ α₀ Ω P hC hcirc)
  exact HarmonicBalls.S11m.CertificateAssembly.firstPass_11_12_corrected_of_inputs hAx hXi hLen hN2 hBase hμW hLoc
    hNonat hFull hgrowth hfr hmass hCMAbs hCMRew hComp hDsm hMf hDiam hMk hS

/-- **Lemma 11.12 (corrected), `CorrectedLemma11_12Stmt`, final form (fp-S11m-11-12-final-discharge, z4).**
`firstPass_11_12_of_inputs` with its two remaining derivable hypotheses discharged by repository theorems:
* `hAff` (`WholePlaneGFFAffineInvariance`) by `HarmonicBalls.wholePlaneGFFAffineInvariance_derived`
  (`FirstPass/S11v/Affine.lean:145`), a theorem with no hypothesis beyond `IsWholePlaneGFF`. Its Proofs-side twin
  `wholePlaneGFFAffineInvariance_proved` (`Proofs/Sec9/AffineInvarianceAssembly.lean:21`) cannot be imported with it:
  `Proofs/Sec9/WholePlaneCovAffine` and `FirstPass/S11v/AffineKernel` both declare `HarmonicBalls.wholePlaneCov_affine`.
* `hgrowth` (`LQGVolumeGrowthAllScalesStmt`, I2) by `HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_stronger_singularity`
  (`Proofs/Sec2/SingularAtomAtZero.lean:59`), from the PROPOSED inputs `hDG`, `hCC`, `hE` and the affine invariance above;
* `hEx` (the case `α₀ = 0` of `hE`) by specialisation.
The S11t N2 step `hS` and `hBase`, `hXi`, `hFull` are discharged inside `firstPass_11_12_of_inputs`.

Remaining hypotheses, with class (file:line of the Prop):
* FROZEN (`FIRST-PASS FROZEN`): `hAx` `LQGMetricFieldAxiomsUnivFrozen` (`Frozen/S11j.lean:143`); `hLen`
  `LQGMetricLengthUnivFrozen` (`Frozen/S11j.lean:133`); `hLoc` `LocalLQGDecoderCommonFrozen` (`Frozen/S11c.lean:386`);
  `hCanon` `LQGCanonicalDecodersExistStmt` (`Frozen/S11n.lean:30`); `hExists` `WholePlaneGFFExistsFrozen`
  (`S11r/Frozen.lean:37`); `hfr` `LQGInternalMetricWeylAeMeasurableFrozen` (`Frozen/S11d.lean:123`); `hmass`
  `LQGMassFunctionalMeasurableFrozen` (`Frozen/S11d.lean:144`); `hCMAbs` `CameronMartinGFFMutualAbsCont`
  (`Frozen/S11d.lean:74`); `hCMRew` `CameronMartinGFFReweighting` (`Frozen/S11aj.lean:31`); `hComp`
  `WeylScalingCompositionFrozen` (`Frozen/S11d.lean:89`); `hMf` `LQGMassInnerMeasurableFrozen` (`Frozen/S11k.lean:58`);
  `hDiam` `LQGInternalDiamInnerMeasurableFrozen` (`Frozen/S11k.lean:74`); `hMk` `DomainMarkovConditionalPositiveFrozen`
  (`Frozen/S11k.lean:43`).
* PROPOSED (universal forms, PENDING operator source-check): `hμW` `LQGMeasureWeylScaling` (`Proposed/LQG.lean:95`);
  `hNonat` `LQGMeasureNonatomicAll` (`S11n/MeasureDecoder.lean:34`, of `Proposed/LQG.lean:77`); `hDG`
  `WholePlaneLQGBallMassBounds` (`Proposed/LQG.lean:154`, Ding-Gwynne Lemma 3.8 route); `hCC` `LQGMeasureCoordChange`
  at `α₀ = 0` (`Proposed/LQG.lean:116`); `hE` `LQGMeasureExistence` for all `α` (`Proposed/LQG.lean:68`).
* NUMBERED (Draft statements of the paper's numbered results): `hDsm` `SmallMetricDiameterLargeMassStmt`
  (Proposition 11.9, `Draft/Section11.lean:201`); `hholder` `GreenPotentialHolderStmt` (Proposition 2.5, Green part,
  `Draft/Section2.lean:190`).
* NOT CLASSIFIED, reported: `hN2` `LocalMetricReplacementStmt` (n2, `S11r/LocalMetricReplacement.lean:53`). The operator's
  04:48 UTC note keeps it as a frozen input, but it is not in a `Frozen/` file, and its docstring cites a ChatGPT answer
  (`CHATGPT-n2-hII.md` §2.2) rather than a published locator. No repository proof was found.
-/
theorem firstPass_11_12_final
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hLen : LQGMetricLengthUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hμW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hmass : LQGMassFunctionalMeasurableFrozen.{u})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{u})
    (hCMRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hDsm : SmallMetricDiameterLargeMassStmt.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u}) :
    CorrectedLemma11_12Stmt.{u} :=
  firstPass_11_12_of_inputs hAx hLen hN2 hμW hLoc hCanon hNonat
    (fun γ Ω _ P hC hcirc => hE Ω P γ 0 hC hcirc)
    (fun _ _ P hC hcirc => HarmonicBalls.wholePlaneGFFAffineInvariance_derived P hC hcirc)
    hExists
    (HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_stronger_singularity hDG
      (fun _ _ P hC hcirc => HarmonicBalls.wholePlaneGFFAffineInvariance_derived P hC hcirc) hCC hE)
    hfr hmass hCMAbs hCMRew hComp hDsm hMf hDiam hMk hholder

end HarmonicBalls.S11m.Final11_12
