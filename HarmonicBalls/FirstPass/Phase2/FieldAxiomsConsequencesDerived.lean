import HarmonicBalls.FirstPass.Phase2.FieldAxiomsDerived
import HarmonicBalls.FirstPass.Phase2.WeylLogTruncationDerivedInputs
import HarmonicBalls.FirstPass.Phase2.WeylContinuousShiftDerived
import HarmonicBalls.FirstPass.Phase2.SupMeasurableDerived
import HarmonicBalls.FirstPass.Phase2.WeylScalingCompositionDerived
import HarmonicBalls.FirstPass.Phase2.WeylShiftedSupDerived2
import HarmonicBalls.FirstPass.Phase2.InnerMeasurableDerived
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsLeafForms
import HarmonicBalls.FirstPass.Closure.Sec11

/-!
# Consequences of the field axioms of the LQG metric, with the axioms supplied

The field axioms of the γ-LQG metric for the log-singular field `h - α₀ log |·|`
(`LQGMetricFieldAxiomsUnivFrozen`, HB Fact 2.2; Gwynne-Miller arXiv:1905.00383, DFGPS arXiv:1905.00380 Theorem 1.10)
are proved in `FieldAxiomsDerived.lean` (`lqgMetricFieldAxiomsUnivFrozen_derived`). Every statement below was proved
earlier from these axioms alone (or from them and statements already proved); here the axioms are supplied, so each
statement holds with no hypothesis.

* the a.e. measurability of the Weyl-scaled internal metric (`LQGInternalMetricWeylAeMeasurableFrozen`);
* the Cameron-Martin event transfer (`CameronMartinEventTransferFrozen`);
* continuity of the metric under a continuous shift of the field, Axiom I (`LQGMetricContinuousShiftFactI`);
* measurability of the supremum of the metric over a compact set (`LQGMetricSupMeasurableFrozen`);
* measurability of the Weyl-shifted supremum on dyadic squares (`WeylShiftedSupMeasurableFrozen`);
* inner measurability of internal diameters (`LQGInternalDiamInnerMeasurableFrozen`);
* Proposition 11.9 (`SmallMetricDiameterLargeMassStmt`), from the axioms and Proposition 11.10;
* Lemma 11.14 (`PinchEventMetricBallConsequenceStmt`) and Lemma 11.15 (`PinchFirstEventPositiveStmt`).
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- The field axioms in the argument order `γ ξ α₀ Ω` used by several consumers. -/
theorem lqgMetricFieldAxioms_forall_derived (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc :=
  lqgMetricFieldAxiomsUnivFrozen_derived.{u} Ω P γ ξ α₀ hC hcirc

/-- **Derived.** A.e. measurability of the Weyl-scaled internal metric. -/
theorem lqgInternalMetricWeylAeMeasurableFrozen_derived : LQGInternalMetricWeylAeMeasurableFrozen.{u} :=
  lqgInternalMetricWeylAeMeasurable_of_fieldAxioms lqgMetricFieldAxiomsUnivFrozen_derived

/-- **Derived.** The Cameron-Martin event transfer for the γ-LQG metric. -/
theorem cameronMartinEventTransferFrozen_derived : CameronMartinEventTransferFrozen.{u} :=
  cameronMartinEventTransfer_of_fieldAxioms lqgMetricFieldAxiomsUnivFrozen_derived

/-- **Derived.** Axiom I in the form of continuity under a continuous shift of the field. -/
theorem lqgMetricContinuousShiftFactI_derived : LQGMetricContinuousShiftFactI.{u} :=
  lqgMetricContinuousShiftFactI_of_fieldAxioms lqgMetricFieldAxiomsUnivFrozen_derived

/-- **Derived.** Measurability of the supremum of the γ-LQG metric over a compact set. -/
theorem lqgMetricSupMeasurableFrozen_derived : LQGMetricSupMeasurableFrozen.{u} :=
  lqgMetricSupMeasurable_of_fieldAxioms lqgMetricFieldAxiomsUnivFrozen_derived

/-- **Derived.** Measurability of the Weyl-shifted supremum over closed dyadic squares. -/
theorem weylShiftedSupMeasurableFrozen_derived : WeylShiftedSupMeasurableFrozen.{u} :=
  weylShiftedSupMeasurable_derived lqgMetricFieldAxiomsUnivFrozen_derived weylScalingCompositionFrozen_holds
    lqgInternalMetricWeylAeMeasurableFrozen_derived

/-- **Derived.** Inner measurability of the internal diameters of the γ-LQG metric. -/
theorem lqgInternalDiamInnerMeasurableFrozen_derived : LQGInternalDiamInnerMeasurableFrozen.{u} :=
  lqgInternalDiamInnerMeasurable_derived lqgMetricFieldAxioms_forall_derived

/-- **Proposition 11.9, derived.** Small metric diameter forces large LQG mass, from the field axioms and
Proposition 11.10 (`S11c.firstPass_11_10_derived`). -/
theorem firstPass_11_9_derived : SmallMetricDiameterLargeMassStmt.{u} :=
  firstPass_11_9_derivedInputsFieldAxioms lqgMetricFieldAxioms_forall_derived S11c.firstPass_11_10_derived

/-- **Lemma 11.14, derived.** The metric-ball consequence of the pinch event. -/
theorem firstPass_11_14_derived : PinchEventMetricBallConsequenceStmt.{u} :=
  Closure.closure_11_14 lqgMetricFieldAxiomsUnivFrozen_derived

/-- **Lemma 11.15, derived.** Positive probability of the first pinch event. -/
theorem firstPass_11_15_derived : PinchFirstEventPositiveStmt.{u} :=
  firstPass_11_15_fieldAxioms lqgMetricFieldAxiomsUnivFrozen_derived.{0}

end HarmonicBalls
