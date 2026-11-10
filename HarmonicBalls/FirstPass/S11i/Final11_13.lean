import HarmonicBalls.FirstPass.Closure.Sec11
import HarmonicBalls.FirstPass.S11i.Step8PhysExists

/-!
# Lemma 11.13 (canonical), first-pass final assembly at universe 0 (fp-S11-13-final-assembly-u0, owner n3)

`HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_final` concludes `CorrectedLemma11_13CanonicalStmt.{0}`
(`HarmonicBalls/FirstPass/S11i/Faithful.lean:102`). Universe 0 is the operator's decision (2026-11-10 17:45 UTC): the paper
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
   file; its B2 target `FP/S11r/LocalMetricReplacement.lean:58` is unproved.
2. `hCal` `Step8EventCalibrationStmt.{0}` (route 2 (c), `S11i/Step8PhysExists.lean:109`): OPEN, owner n1, math pending. Needs a
   pinch event `E` whose common probability equals that of a coding event `F` with the insertion-zero unit frequency.
3. `hIns` `Step8InsertionTransferStmt` (route 2 (b), `S11i/Step8PhysExists.lean:94`): OPEN, owner n4, in progress
   (`S11i/InsertionTransfer.lean`).
4. `hCC0` `CoordChangeZeroStmt` (`S11i/Step8PhysExists.lean:101`): PROPOSED, `Proposed/LQG.lean:116`, pending operator source-check.
5. PROPOSED, pending operator source-check: `hμW` (`Proposed/LQG.lean:95`), `hNonat` (`Proposed/LQG.lean:77`), `hDG`
   (`Proposed/LQG.lean:154`), `hE` (`Proposed/LQG.lean:68`).
6. FROZEN (first-pass frozen axioms `FP/Frozen/*.lean`, `FP/S11r/Frozen.lean`, `FP/S11n`, or the cited Draft statement
   `GreenPotentialHolderStmt`, `Draft/Section2.lean:190`, listed in `docs/campaign/FROZEN.md`): `hAx`, `hLen`, `hLoc`, `hCanon`,
   `hExists`, `hfr`, `hmass`, `hCMAbs`, `hCMRew`, `hComp`, `hMf`, `hDiam`, `hMk`, `hholder`, `hShift`, `hFD`, `hDC`, `hCMT`,
   `hPos10`, `hMassM`, `hSupM`, `hFin`, `hW`, `hM1`, `hM2`. Per-binder file:line as in `S11i/Assembly11_13.lean` (module docstring).

Universe-0 use of the counted 11.11 and 1.2 canonical theorems: see the report `reports/n3.md`.
-/

namespace HarmonicBalls.FirstPassS11iFinal11_13

open MeasureTheory

/-- **Lemma 11.13 (canonical), first-pass final assembly, universe 0.** `CorrectedLemma11_13CanonicalStmt.{0}` from the
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

end HarmonicBalls.FirstPassS11iFinal11_13

#print axioms HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_final
