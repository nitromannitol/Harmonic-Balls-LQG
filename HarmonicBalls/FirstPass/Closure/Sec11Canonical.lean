import HarmonicBalls.FirstPass.Closure.Sec11
import HarmonicBalls.FirstPass.Closure.Bridge12Canonical
import HarmonicBalls.FirstPass.S8c.WeylOffOriginDerived
import HarmonicBalls.FirstPass.Canonical.Stmts
import HarmonicBalls.FirstPass.Canonical.NotMetricBall

/-!
# Closure of Proposition 11.11, canonical copy chain

`closure_11_11_canonical` is `closure_11_11` (`FirstPass/Closure/Sec11.lean`) with three changes, all mechanical:
* the Lemma 11.13 input is the canonical one: `closure_11_13_canonical` (`Sec11.lean`, canonical exponent
  `ξ = lqgXi γ`, model fixed before the density), converted to `ManyPinchScalesCanonicalModelStmt` by
  `manyPinchScalesCanonicalModel_of_canonical` (`Bridge12Canonical.lean`);
* the assembly is `firstPass_11_11_canonical` (`FirstPass/Canonical/NotMetricBall.lean`), with conclusion
  `HarmonicBallNotMetricBallCanonicalStmt` (`FirstPass/Canonical/Stmts.lean`);
* there is no `hWeyl` binder: the input `LocalLQGInsertionWeylOffOrigin` of `closure_11_6` is supplied by
  `localLQGInsertionWeylOffOrigin_derived` (`FirstPass/S8c/WeylOffOriginDerived.lean`).

The hypothesis `hCC` keeps the general insertion `α₀` of `closure_11_11`; it is specialised to `α₀ = 0` for
`closure_11_13_canonical`, whose input uses `LQGMeasureCoordChange P γ 0`. The hypotheses are those of `closure_11_11`
(minus `hWeyl` and `hStep8`) together with those of `closure_11_13_canonical` (the `closure_11_12` chain, with frozen and
Proposed inputs as there). The paper-owned open input is `hId = Step8IdentityGivenPinchEventCanonicalStmt`
(`FirstPass/S11i/Corrected11_13.lean:109`, part (d) of Lemma 11.13), the same single open hypothesis as in
`closure_11_13_canonical`.
-/

universe u

namespace HarmonicBalls.Closure

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- **Closure of Proposition 11.11, canonical form** (`HarmonicBallNotMetricBallCanonicalStmt`,
`firstPass_11_11_canonical`). Canonical Weyl exponent `ξ = lqgXi γ` in the Lemma 11.13 input, model fixed before the
density; the only paper-owned open hypothesis is `hId` (part (d) of Lemma 11.13). -/
theorem closure_11_11_canonical
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u}) (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    -- inputs of `closure_11_13_canonical` (the `closure_11_12` chain), in its order, except `hAx`, `hE`, `hDG`
    (hLen : LQGMetricLengthUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hμW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hmass : LQGMassFunctionalMeasurableFrozen.{u})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{u})
    (hCMRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u}) (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u}) (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u}) (hMassM : LQGMeasureSquareMeasurableFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u}) (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hWIC : WeylInternalClosedFrozen)
    (hM1 : WeylShiftedSupMeasurableFrozen.{u}) (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u}) :
    HarmonicBallNotMetricBallCanonicalStmt.{u} := by
  have h13 : CorrectedLemma11_13CanonicalStmt.{u} :=
    closure_11_13_canonical hAx hLen hN2 hμW hLoc hCanon hNonat hExists hDG
      (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE hfr hmass hCMAbs hCMRew hComp hMf hDiam hMk hholder
      hShift hFD hDC hCMT hPos10 hMassM hSupM hFin hWIC hM1 hM2 hId
  exact firstPass_11_11_canonical
    (closure_11_6 hDG hCC hE hW hN hL1 localLQGInsertionWeylOffOrigin_derived hE1 hE3 hB)
    (manyPinchScalesCanonicalModel_of_canonical h13)
    (volumeGrowthI2_of_staged hDG hCC hW hE hN)
    (fun γ α₀ ξ _ _ _ Ω _ P hC hcirc _ => hAx Ω P γ ξ α₀ hC hcirc)

end HarmonicBalls.Closure
