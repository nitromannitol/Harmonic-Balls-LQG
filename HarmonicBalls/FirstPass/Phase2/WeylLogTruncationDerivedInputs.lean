import HarmonicBalls.FirstPass.Phase2.InternalMetricWeylAeMeasurableDerived
import HarmonicBalls.FirstPass.Phase2.DerivedInputsContinuousShift
import HarmonicBalls.FirstPass.Phase2.WeylShiftedChainDerived
import LatticeProb.LQG.WeylLogTruncation

/-!
# Internal-metric measurability and the Cameron-Martin event transfer from the field axioms

The truncation limit of the singular Weyl scaling (`WeylLogTruncationStatement`) is the library theorem
`LatticeProb.LQG.IsEuclideanLengthMetric.tendsto_weylScaling_logCutoff`. With it, the two statements derived in
`InternalMetricWeylAeMeasurableDerived` follow from the field axioms of the singular metric alone:

* `lqgInternalMetricWeylAeMeasurable_of_fieldAxioms`: almost sure measurability of the internal metric of the
  singular LQG metric on an open set (`LQGInternalMetricWeylAeMeasurableFrozen`);
* `cameronMartinEventTransfer_of_fieldAxioms`: the Cameron-Martin event transfer (`CameronMartinEventTransferFrozen`).

Consequently Proposition 11.9 and Lemma 11.10 hold without these two hypotheses:
`firstPass_11_9_derivedInputsFieldAxioms` and `S11c.firstPass_11_10_derivedInputsFieldAxioms`. The kept hypotheses
are unchanged; the proofs are chains of applications.
-/

namespace HarmonicBalls

universe u

open MeasureTheory

/-- The truncation limit of the singular Weyl scaling holds: it is
`LatticeProb.LQG.IsEuclideanLengthMetric.tendsto_weylScaling_logCutoff`. -/
theorem weylLogTruncationStatement_holds : WeylLogTruncationStatement :=
  fun _ hD ξ α₀ _ hF _ hr0 hr hlim hcont u v =>
    hD.tendsto_weylScaling_logCutoff ξ α₀ hF hr0 hr hlim hcont u v

/-- **Derived.** Almost sure measurability of the internal metric of the singular LQG metric
(`LQGInternalMetricWeylAeMeasurableFrozen`) from the field axioms of the singular metric
(`LQGMetricFieldAxiomsUnivFrozen`) alone. -/
theorem lqgInternalMetricWeylAeMeasurable_of_fieldAxioms (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    LQGInternalMetricWeylAeMeasurableFrozen.{u} :=
  lqgInternalMetricWeylAeMeasurable_of_fieldAxioms_of_truncation hAx weylLogTruncationStatement_holds

/-- **Derived.** The Cameron-Martin event transfer (`CameronMartinEventTransferFrozen`) from the field axioms of the
singular metric (`LQGMetricFieldAxiomsUnivFrozen`) alone. -/
theorem cameronMartinEventTransfer_of_fieldAxioms (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    CameronMartinEventTransferFrozen.{u} :=
  cameronMartinEventTransfer_of_fieldAxioms_of_truncation hAx weylLogTruncationStatement_holds

/-- `SmallMetricDiameterLargeMassStmt` (Proposition 11.9) from the hypotheses `hAx`, `h1110` of
`firstPass_11_9_derivedInputsContinuousShift` alone: the hypothesis `hMet` of that declaration is supplied by
`lqgInternalMetricWeylAeMeasurable_of_fieldAxioms` from `hAx`. -/
theorem firstPass_11_9_derivedInputsFieldAxioms
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (h1110 : SmallMetricDiameterLargeMassSquareStmt.{u}) :
    SmallMetricDiameterLargeMassStmt.{u} :=
  firstPass_11_9_derivedInputsContinuousShift
    (lqgInternalMetricWeylAeMeasurable_of_fieldAxioms fun Ω _ P γ ξ α₀ hC hcirc => hAx γ ξ α₀ Ω P hC hcirc)
    hAx h1110

/-- `SmallMetricDiameterLargeMassSquareStmt` (Lemma 11.10) from the hypotheses `hDC`, `hPos`, `hFin`, `hAx` of
`S11c.firstPass_11_10_derivedInputsWeylShiftedSup` alone: the hypothesis `hCM` of that declaration is supplied by
`cameronMartinEventTransfer_of_fieldAxioms` from `hAx`. -/
theorem S11c.firstPass_11_10_derivedInputsFieldAxioms
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hPos : LQGMeasureSquarePositiveFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc) :
    SmallMetricDiameterLargeMassSquareStmt.{u} :=
  S11c.firstPass_11_10_derivedInputsWeylShiftedSup hDC
    (cameronMartinEventTransfer_of_fieldAxioms fun Ω _ P γ ξ α₀ hC hcirc => hAx γ ξ α₀ Ω P hC hcirc)
    hPos hFin hAx

end HarmonicBalls
