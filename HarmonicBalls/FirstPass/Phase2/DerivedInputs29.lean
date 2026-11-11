import HarmonicBalls.FirstPass.Phase2.DerivedInputs3
import HarmonicBalls.FirstPass.Phase2.DerivedInputs11
import HarmonicBalls.FirstPass.Phase2.DerivedInputs19
import HarmonicBalls.Proofs.Sec2.Assembly
import HarmonicBalls.Proofs.Sec2.SingularAtomAtZero
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling

/-!
# Binder trades of rows 40 and 50 to rows 1, 2, 3

Decision R60: the Draft statements `LQGMeasureFullSupportStmt`
and `LQGVolumeGrowthAllScalesStmt` reduce to the three literature inputs of
Proposed/LQG.lean named in PHASE2-DERIVATION-STATUS.md:

* row 1 `LQGMeasureExistence` (Proposed/LQG.lean:74), used at every `α` (row 4 needs existence at every `α₀`);
* row 2 `LQGMeasureCoordChange` (Proposed/LQG.lean:131), used at `α₀ = 0`;
* row 3 `WholePlaneLQGBallMassBounds` (Proposed/LQG.lean:172).

The other premises are derived: `WholePlaneGFFAffineInvariance_derived`,
`HarmonicBalls.Section6.lqgMeasureWeylScaling`, and row 4 `LQGMeasureNonatomic`
through `singular_nonatomic_of_existence_and_wholePlane` (Proofs/Sec2/SingularAtomAtZero.lean). The two statements then follow from
`lqgMeasureFullSupportStmt_of_literature` (Proofs/Sec2/Assembly.lean:124) and `lqgVolumeGrowthAllScalesStmt_of_literature`
(Proofs/Sec2/Assembly.lean:120).

Wrappers (counted chains, newest round of each chain; the older members are unchanged):
* `firstPass_8_2_S8d_noWeyl_derivedInputs29` (DerivedInputs19.lean:27 chain): binder `hfull` removed; binder count 6 → 5.
* `HarmonicBalls.FirstPassS11iFinal11_13Close.firstPass_11_13_closed_derivedInputs29` (DerivedInputs3.lean:165 chain):
  binders `hFull` and `hgrowth` removed; binder count 37 → 35. Rows 1-3 are already bound (`hE`, `hCCα`, `hDG`).

Conclusions are unchanged. No binder is added.
-/

open MeasureTheory

universe u

namespace HarmonicBalls

/-- Row 4 `LQGMeasureNonatomic` at every `α₀`, from rows 1, 2, 3 (`singular_nonatomic_of_existence_and_wholePlane`). -/
theorem lqgMeasureNonatomic_of_rows123
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc :=
  singular_nonatomic_of_existence_and_wholePlane hDG WholePlaneGFFAffineInvariance_derived hCC hE

/-- Row 40 `LQGMeasureFullSupportStmt` (I1, Draft/Section2.lean:109) from the literature rows 1, 2, 3. -/
theorem lqgMeasureFullSupportStmt_of_rows123
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc) :
    LQGMeasureFullSupportStmt.{u} :=
  lqgMeasureFullSupportStmt_of_literature hDG WholePlaneGFFAffineInvariance_derived hCC
    (fun Ω _ P γ hC hcirc => Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc)
    (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc)
    (lqgMeasureNonatomic_of_rows123 hDG hCC hE)

/-- Row 50 `LQGVolumeGrowthAllScalesStmt` (I2, Draft/Section2.lean:122) from the literature rows 1, 2, 3. -/
theorem lqgVolumeGrowthAllScalesStmt_of_rows123
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc) :
    LQGVolumeGrowthAllScalesStmt.{u} :=
  lqgVolumeGrowthAllScalesStmt_of_literature hDG WholePlaneGFFAffineInvariance_derived hCC
    (fun Ω _ P γ hC hcirc => Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc)
    (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc)
    (lqgMeasureNonatomic_of_rows123 hDG hCC hE)

/-- Binder trade of `firstPass_8_2_S8d_noWeyl_derivedInputs19` (DerivedInputs19.lean:27): the binder `hfull` is
derived from `hDG`, `hCC` (at `α₀ = 0`) and `hEx`, which the wrapper already binds. Binder count 6 → 5. -/
theorem firstPass_8_2_S8d_noWeyl_derivedInputs29
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hEx : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0}) :
    TypicalPointManyGoodScalesStmt.{u} :=
  HarmonicBalls.firstPass_8_2_S8d_noWeyl_derivedInputs17 (hL1 := hL1)
    (hfull := lqgMeasureFullSupportStmt_of_rows123 hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hEx)
    (hL67 := (HarmonicBalls.Closure.closure_6_7 hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hEx))
    (hEx := hEx)
    (hN := (fun Ω _ P γ α hC hcirc => HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG
      (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hEx γ α Ω P hC hcirc))
    (hCC := hCC) (hE3 := hE3)

end HarmonicBalls

namespace HarmonicBalls.FirstPassS11iFinal11_13Close

open MeasureTheory Metric Set Filter Topology
open HarmonicBalls.FirstPassS11iFinal11_13

/-- Binder trade of `firstPass_11_13_closed_derivedInputs3` (DerivedInputs3.lean:165): the binders `hFull` and
`hgrowth` are derived from `hDG`, `hCCα` (at `α₀ = 0`) and `hE`, which the wrapper already binds. Binder count 37 → 35. -/
theorem firstPass_11_13_closed_derivedInputs29
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hLen : LQGMetricLengthUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
    (hμW : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{0})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
    (hmass : LQGMassFunctionalMeasurableFrozen.{0})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{0})
    (hCMRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{0})
    (hComp : WeylScalingCompositionFrozen.{0})
    (hMf : LQGMassInnerMeasurableFrozen.{0})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{0})
    (hMk : DomainMarkovConditionalPositiveFrozen.{0})
    (hholder : GreenPotentialHolderStmt.{0})
    (hShift : LQGMetricContinuousShiftFactI.{0})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{0})
    (hCMT : CameronMartinEventTransferFrozen.{0})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{0})
    (hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hDsm : SmallMetricDiameterLargeMassStmt.{0})
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : CorrectedLemma11_13CanonicalStmt.{0} :=
  HarmonicBalls.FirstPassS11iFinal11_13Close.firstPass_11_13_closed_derivedInputs2 hAx hLen hN2 hμW hLoc hCanonM
    hNonat hExists hDG hCCα hE hfr hmass hCMAbs hCMRew hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10
    (HarmonicBalls.lqgMeasureSquareMeasurable_derived.{0} hmeasure) hSupM hFin HarmonicBalls.weylInternalClosed_derived
    hM1 hRootCont hProf hWCont hA10
    (HarmonicBalls.lqgMeasureFullSupportStmt_of_rows123.{0} hDG (fun Ω _ P γ hC hcirc => hCCα γ 0 Ω P hC hcirc) hE)
    (HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_rows123.{0} hDG (fun Ω _ P γ hC hcirc => hCCα γ 0 Ω P hC hcirc) hE)
    hDsm hK

end HarmonicBalls.FirstPassS11iFinal11_13Close
