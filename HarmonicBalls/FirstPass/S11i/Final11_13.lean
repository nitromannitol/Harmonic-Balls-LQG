import HarmonicBalls.FirstPass.Closure.Sec11
import HarmonicBalls.FirstPass.S11i.Step8PhysExists
import HarmonicBalls.FirstPass.S11i.InsertionTransfer
import HarmonicBalls.FirstPass.Frozen.S11rMetric

/-!
# Lemma 11.13 (canonical), final assembly at universe 0

`HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_final` concludes `CorrectedLemma11_13CanonicalStmt.{0}`
(`HarmonicBalls/FirstPass/S11i/Faithful.lean:102`). Universe 0 is fixed: the paper
has no universe content and every producer is at `Type`. The universe-general adapter is
`step8Identity_given_pinchEvent_canonical_of_physExists.{w}` (`S11i/Step8PhysExists.lean`); route 2 reaches only universe 0,
because `zoomMetricNormStmt_of_isLQGMetricOfField` takes `Ω₀ : Type` (`S11i/HzoomScale.lean:275`).

Route. `HarmonicBalls.Closure.closure_11_13_canonical.{0}` (`Closure/Sec11.lean:400`) with its part (d) input
`Step8IdentityGivenPinchEventCanonicalStmt.{0}` (`S11i/Corrected11_13.lean:109`) supplied by the route-2 adapter
`step8Identity_given_pinchEvent_canonical_of_route2 hCC0 hCal hIns` (`S11i/Step8PhysExists.lean`). Part (c), the Lemma 11.12
event, is `closure_11_12` through `pinchEventGamma_exists` inside `closure_11_13_canonical`, as in `S11i/Assembly11_13.lean`.

Binder changes against `closure_11_13_canonical`. `hId` is removed (derived by the adapter). `hCC` (`LQGMeasureCoordChange P γ 0`
for every whole-plane model) is the same proposition as `CoordChangeZeroStmt`, so it is bound once, as `hCC0`. Added: `hCal`, `hIns`.
Nothing is weakened; no hypothesis is added beyond the named inputs below.

OPEN list (no provider; the theorem is complete once these are discharged):
1. `hN2` `LocalMetricReplacementStmt` (all `γ ξ`, disks in `ball 0 1` form): OPEN, classification pending. Not in a `Frozen/`
   file; its target `FP/S11r/LocalMetricReplacement.lean:58` is unproved.
2. `hCal` `Step8EventCalibrationStmt.{0}` (route 2 (c), `S11i/Step8PhysExists.lean:109`): OPEN, math pending. Needs a
   pinch event `E` whose common probability equals that of a coding event `F` with the insertion-zero unit frequency.
3. `hIns` `Step8InsertionTransferStmt` (route 2 (b), `S11i/Step8PhysExists.lean:94`): OPEN
   (`S11i/InsertionTransfer.lean`).
4. `hCC0` `CoordChangeZeroStmt` (`S11i/Step8PhysExists.lean:101`): PROPOSED, `Proposed/LQG.lean:116`, pending source-check.
5. PROPOSED, pending source-check: `hμW` (`Proposed/LQG.lean:95`), `hNonat` (`Proposed/LQG.lean:77`), `hDG`
   (`Proposed/LQG.lean:154`), `hE` (`Proposed/LQG.lean:68`).
6. FROZEN (`FP/S11r/Frozen.lean`, `FP/S11n`, or the cited Draft statement
   `GreenPotentialHolderStmt`, `Draft/Section2.lean:190`): `hAx`, `hLen`, `hLoc`, `hCanon`,
   `hExists`, `hfr`, `hmass`, `hCMAbs`, `hCMRew`, `hComp`, `hMf`, `hDiam`, `hMk`, `hholder`, `hShift`, `hFD`, `hDC`, `hCMT`,
   `hPos10`, `hMassM`, `hSupM`, `hFin`, `hW`, `hM1`, `hM2`. Per-binder file:line as in `S11i/Assembly11_13.lean` (module docstring).

Universe-0 use of the counted 11.11 and 1.2 canonical theorems.
-/

namespace HarmonicBalls.FirstPassS11iFinal11_13

open MeasureTheory

/-- **Lemma 11.13 (canonical), final assembly, universe 0.** `CorrectedLemma11_13CanonicalStmt.{0}` from the
frozen and proposed inputs (classes in the module docstring) and the named inputs `hN2`, `hCal`, `hIns`, `hCC0`. The only
open named inputs are `hN2`, `hCal`, `hIns`; `hCC0` is Proposed. -/
theorem firstPass_11_13_final
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hLen : LQGMetricLengthUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hμW : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hCanon : LQGCanonicalDecodersExistStmt.{0})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{0})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC0 : HarmonicBalls.FirstPassS11iStep8PhysExists.CoordChangeZeroStmt)
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
    (hShift : LQGMetricContinuousShiftFactI.{0}) (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{0}) (hCMT : CameronMartinEventTransferFrozen.{0})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0}) (hMassM : LQGMeasureSquareMeasurableFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0}) (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hW : WeylInternalClosedFrozen)
    (hM1 : WeylShiftedSupMeasurableFrozen.{0}) (hM2 : WeylShiftedMassMeasurableFrozen.{0})
    (hCal : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{0})
    (hIns : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8InsertionTransferStmt) :
    CorrectedLemma11_13CanonicalStmt.{0} :=
  HarmonicBalls.Closure.closure_11_13_canonical.{0} hAx hLen hN2 hμW hLoc hCanon hNonat hExists hDG
    (fun Ω _ P γ hC hcirc => hCC0 γ Ω P hC hcirc) hE hfr hmass hCMAbs hCMRew hComp hMf hDiam hMk hholder hShift hFD
    hDC hCMT hPos10 hMassM hSupM hFin hW hM1 hM2
    (HarmonicBalls.FirstPassS11iStep8PhysExists.step8Identity_given_pinchEvent_canonical_of_route2 hCC0 hCal hIns)

/-! ### Route-1 variant

`firstPass_11_13_final` (route 2) is kept unchanged. The route-1 variant takes the scale transfer at insertion `α` from the
scale `0` only (`Step8InsertionTransferK0Stmt`, named binder) and the normalization of the metric
(`zoomMetricNormAlpha_of_isLQGMetricOfField`, proved in `S11i/ZoomMetricAlpha0.lean`). The measure normalization at insertion
`α` needs the coordinate change at `α` (`CoordChangeAlpha0Stmt`, Proposed, pending source-check); it also gives the
closure's `hCC` at `α = 0`, so `hCC0` is not a separate binder here.

OPEN list of the route-1 variant (named binders, exact types):
1. `hN2` `LocalMetricReplacementStmt` (classification pending, as in route 2).
2. `hCal` `Step8EventCalibrationStmt.{0}` (route 1 (c), `S11i/Step8PhysExists.lean`): OPEN, math pending.
3. `hK0` `Step8InsertionTransferK0Stmt` (route 1 (b) at `k = 0`): OPEN (`allModelsAt_insertion_of_zero_k0`).
4. `hCCα` `CoordChangeAlpha0Stmt.{0}` (`Proposed/LQG.lean:116`, Fact 2.1 IV at every `α`): PROPOSED, pending source-check.
5. PROPOSED, pending source-check: `hμW`, `hNonat`, `hDG`, `hE` (as in route 2).
6. FROZEN: the remaining binders (as in route 2). -/

theorem firstPass_11_13_final_route1
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hLen : LQGMetricLengthUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hμW : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hCanon : LQGCanonicalDecodersExistStmt.{0})
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
    (hShift : LQGMetricContinuousShiftFactI.{0}) (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{0}) (hCMT : CameronMartinEventTransferFrozen.{0})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0}) (hMassM : LQGMeasureSquareMeasurableFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0}) (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hW : WeylInternalClosedFrozen)
    (hM1 : WeylShiftedSupMeasurableFrozen.{0}) (hM2 : WeylShiftedMassMeasurableFrozen.{0})
    (hCal : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{0})
    (hK0 : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8InsertionTransferK0Stmt) :
    CorrectedLemma11_13CanonicalStmt.{0} :=
  HarmonicBalls.Closure.closure_11_13_canonical.{0} hAx hLen hN2 hμW hLoc hCanon hNonat hExists hDG
    (fun Ω _ P γ hC hcirc => hCCα γ 0 Ω P hC hcirc) hE hfr hmass hCMAbs hCMRew hComp hMf hDiam hMk hholder hShift hFD
    hDC hCMT hPos10 hMassM hSupM hFin hW hM1 hM2
    (HarmonicBalls.FirstPassS11iStep8PhysExists.step8Identity_given_pinchEvent_canonical_of_route1 hCCα hCal hK0)

/-! ### Background projections for the counted theorem

Step 1: the measurable canonical decoders, the universe-0 metric axioms and the exponent positivity are
derived from the frozen inputs of the signature, not added as binders. -/

/-- The weak canonical decoder statement `LQGCanonicalDecodersExistStmt` (`Frozen/S11n.lean:33`) is the projection of the
measurable one (`Frozen/S11n.lean:71`): forget the kernel, the metric map, their measurability and the conull set `G`. -/
theorem lqgCanonicalDecodersExist_of_measurable (h : LQGCanonicalDecodersMeasurableExistStmt.{0}) :
    LQGCanonicalDecodersExistStmt.{0} := by
  intro γ ξ α₀ h0 h1 h2
  obtain ⟨K, d, -, -, -, hId, -⟩ := h γ ξ α₀ h0 h1 h2
  exact ⟨fun L => K L, fun L x y => d L (x, y), hId⟩

/-- The universe-0 metric axioms `LQGMetricSatisfiesAxiomsUnivFrozen.{0}` (`Frozen/S11g.lean:31`) are the Defs field
`IsLQGMetric.satisfiesLQGMetricAxioms` (`Defs/LQGMetric.lean:183`) at `Ω : Type`: no universe transfer is needed. -/
theorem lqgMetricSatisfiesAxiomsUnivFrozen_zero : LQGMetricSatisfiesAxiomsUnivFrozen.{0} :=
  fun _ _ _ h Ω _ P hC hcirc f h1 h2 h3 => h.satisfiesLQGMetricAxioms Ω P hC hcirc f h1 h2 h3

/-- `LQGMetricExponentPositive` (`Frozen/S11j.lean:105`) from `hExists` and the derived whole-plane affine invariance
(`wholePlaneGFFAffineInvariance_derived`, `S11v/Affine.lean:145`), through `lqgMetricExponentPositive_of_inputs`. -/
theorem lqgMetricExponentPositive_derived (hExists : WholePlaneGFFExistsFrozen.{0}) :
    LQGMetricExponentPositive :=
  lqgMetricExponentPositive_of_inputs hExists
    (fun _ _ P hC hcirc => HarmonicBalls.wholePlaneGFFAffineInvariance_derived P hC hcirc)

/-! ### Counted Lemma 11.13, universe 0

`firstPass_11_13` is the counted theorem `CorrectedLemma11_13CanonicalStmt.{0}`. It is the route-1 assembly
(`firstPass_11_13_final_route1`) with two changes:
* the insertion transfer at `k = 0` (`hK0`) is discharged by
  `HarmonicBalls.FirstPassS11iInsertionTransfer.allModelsAt_insertion_of_zero_k0` (`S11i/InsertionTransfer.lean:485`). Its binders are threaded: `hCM := hCMRew`; `hEx := hE` at `α = 0`; `hNon := hNonat` at `α`;
  `hK` the frozen binder below; `hR := hN2` at `ξ = lqgXi γ` (`0 < lqgXi γ` by `lqgGraphDimension_pos`,
  `Defs/LQGGraphDistance.lean:110`); `hLF := hAx`. The binder `hK0` disappears; the new binder is `hK`.
* `hN2`, which is also `hR`, is the frozen wrapper `LocalMetricReplacementFrozen` (`Frozen/S11rMetric.lean:33`), bound once.

Binder classes (FROZEN / PROPOSED / OPEN), with the definition of each Prop:
* FROZEN: `hAx` `LQGMetricFieldAxiomsUnivFrozen` (`Frozen/S11j.lean:155`); `hLen` `LQGMetricLengthUnivFrozen` (`Frozen/S11j.lean:133`);
  `hN2` `LocalMetricReplacementFrozen` (`Frozen/S11rMetric.lean:33`, new); `hLoc` `LocalLQGDecoderCommonFrozen`
  (`Frozen/S11c.lean:388`); `hCanonM` `LQGCanonicalDecodersMeasurableExistStmt` (`Frozen/S11n.lean:71`, replaces the weak `hCanon`; the weak form
  `LQGCanonicalDecodersExistStmt`, `Frozen/S11n.lean:33`, is its projection); `hExists`
  `WholePlaneGFFExistsFrozen` (`S11r/Frozen.lean:39`); `hfr` `LQGInternalMetricWeylAeMeasurableFrozen` (`Frozen/S11d.lean:130`);
  `hmass` `LQGMassFunctionalMeasurableFrozen` (`Frozen/S11d.lean:155`); `hCMAbs` `CameronMartinGFFMutualAbsCont`
  (`Frozen/S11d.lean:74`); `hCMRew` `CameronMartinGFFReweighting` (`Frozen/S11aj.lean:33`); `hComp` `WeylScalingCompositionFrozen`
  (`Frozen/S11d.lean:91`); `hMf` `LQGMassInnerMeasurableFrozen` (`Frozen/S11k.lean:66`); `hDiam`
  `LQGInternalDiamInnerMeasurableFrozen` (`Frozen/S11k.lean:89`); `hMk` `DomainMarkovConditionalPositiveFrozen`
  (`Frozen/S11k.lean:45`); `hholder` `GreenPotentialHolderStmt` (`Draft/Section2.lean:190`, cited Draft statement);
  `hShift` `LQGMetricContinuousShiftFactI` (`Frozen/S11d.lean:34`); `hFD` `PlaneDomainMinusConvexCompactPreconnectedFrozen`
  (`Frozen/S11d.lean:26`); `hDC` `DyadicCellDiamSmallFrozen` (`Frozen/S11c.lean:67`); `hCMT` `CameronMartinEventTransferFrozen`
  (`Frozen/S11c.lean:149`); `hPos10` `LQGMeasureSquarePositiveFrozen` (`Frozen/S11c.lean:130`); `hMassM`
  `LQGMeasureSquareMeasurableFrozen` (`Frozen/S11c.lean:117`); `hSupM` `LQGMetricSupMeasurableFrozen` (`Frozen/S11c.lean:105`);
  `hFin` `ConnectedSquareUnionDiamFiniteFrozen` (`Frozen/S11c.lean:91`); `hW` `WeylInternalClosedFrozen`
  (`Frozen/S11c.lean:180`); `hM1` `WeylShiftedSupMeasurableFrozen` (`Frozen/S11c.lean:217`); `hM2`
  `WeylShiftedMassMeasurableFrozen` (`Frozen/S11c.lean:233`); `hK` `LocalMeasureKernelStmt` (`S11r/Frozen.lean:144`, quantified over
  `γ c₁ c₂ r₁ r₂`).
* PROPOSED (pending source-check): `hμW` `LQGMeasureWeylScaling` (`Proposed/LQG.lean:95`); `hNonat`
  `LQGMeasureNonatomicAll` (`S11n/MeasureDecoder.lean:39`, through `LQGMeasureNonatomic`, `Proposed/LQG.lean:77`); `hDG`
  `WholePlaneLQGBallMassBounds` (`Proposed/LQG.lean:154`); `hCCα` `CoordChangeAlpha0Stmt` (`S11i/Step8PhysReduction.lean:81`, through
  `LQGMeasureCoordChange` at every `α`, `Proposed/LQG.lean:116`); `hE` `LQGMeasureExistence` (`Proposed/LQG.lean:68`).
* OPEN: `hCal` `Step8EventCalibrationStmt.{0}` (`S11i/Step8PhysExists.lean:110`, calibration of the pinch event).
  Discharged by `insertionZeroUnit_of_href` (`S11i/InsertionZeroUnitE.lean:41`) only with its named `hHref` input, not yet
  wired here. The binder is kept.

Step 1: the rooted route (`S11r/RootedHrefBall.lean:28`) needs the frozen inputs
`hBirk`, `hRootCont`, `hProf`, `hWCont`, `hA10` (universal `DMSLemmaA10WholePlaneMarkedSub`, `Frozen/S11i.lean:58`), threaded
here with underscore names (`_hBirk`, `_hRootCont`, `_hProf`, `_hWCont`, `_hA10`) because their consumer is the step-5
`hHref`, not yet wired; the underscore is removed when they are consumed. The universe-0 metric axioms and the exponent
positivity are derived (`lqgMetricSatisfiesAxiomsUnivFrozen_zero`, `lqgMetricExponentPositive_derived`), not binders.

Positional binders are listed in the order of the theorem signature. -/
theorem firstPass_11_13
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
    (hShift : LQGMetricContinuousShiftFactI.{0}) (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{0}) (hCMT : CameronMartinEventTransferFrozen.{0})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0}) (hMassM : LQGMeasureSquareMeasurableFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0}) (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hW : WeylInternalClosedFrozen)
    (hM1 : WeylShiftedSupMeasurableFrozen.{0}) (hM2 : WeylShiftedMassMeasurableFrozen.{0})
    (_hBirk : BirkhoffPointwiseErgodic.{0})
    (_hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (_hProf : LQGMeasureOfProfileMeasurableFrozen.{0})
    (_hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (_hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hCal : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{0})
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂) :
    CorrectedLemma11_13CanonicalStmt.{0} :=
  have hK0 : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8InsertionTransferK0Stmt :=
    fun γ α _ _ _ _ _ _ _ _ _ hgeom hγ0 hγ2 hα h0 =>
      HarmonicBalls.FirstPassS11iInsertionTransfer.allModelsAt_insertion_of_zero_k0 hgeom hγ0 hγ2 hα hCMRew
        (fun Ω _ P hC hcirc => hE Ω P γ 0 hC hcirc)
        (fun Ω _ P hC hcirc => hNonat γ α Ω P hC hcirc)
        (hK γ)
        (fun c₁ c₂ r₁ r₂ =>
          hN2 γ (lqgXi γ) hγ0 hγ2 (div_pos hγ0 (HarmonicBalls.lqgGraphDimension_pos γ)) c₁ c₂ r₁ r₂)
        hAx h0
  HarmonicBalls.Closure.closure_11_13_canonical.{0} hAx hLen hN2 hμW hLoc (lqgCanonicalDecodersExist_of_measurable hCanonM)
    hNonat hExists hDG (fun Ω _ P γ hC hcirc => hCCα γ 0 Ω P hC hcirc) hE hfr hmass hCMAbs hCMRew hComp hMf hDiam hMk
    hholder hShift hFD hDC hCMT hPos10 hMassM hSupM hFin hW hM1 hM2
    (HarmonicBalls.FirstPassS11iStep8PhysExists.step8Identity_given_pinchEvent_canonical_of_route1 hCCα hCal hK0)

end HarmonicBalls.FirstPassS11iFinal11_13

