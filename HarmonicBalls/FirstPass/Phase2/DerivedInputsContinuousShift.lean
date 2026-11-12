import HarmonicBalls.FirstPass.Phase2.DerivedInputs38
import HarmonicBalls.FirstPass.Phase2.WeylContinuousShiftDerived

/-!
# Derived-input forms: Fact 2.2 I for continuous shifts supplied from the field axioms

The counted forms of Proposition 11.9 (`firstPass_11_9_derivedInputs38`) and Lemma 11.10
(`S11c.firstPass_11_10_derivedInputs38`), `FirstPass/Phase2/DerivedInputs38.lean`, bind both the field axioms
`LQGMetricFieldAxiomsUnivFrozen` (Fact 2.2 I-IV for `h = h^ℂ - α₀ log |·|`) and Fact 2.2 I for the shifted field
`h + g`, `g` continuous (`LQGMetricContinuousShiftFactI`). The second follows from the first at the same universe
(`lqgMetricContinuousShiftFactI_of_fieldAxioms`, `FirstPass/Phase2/WeylContinuousShiftDerived.lean`). Each theorem
below has the conclusion of the wrapped declaration and its hypotheses with `LQGMetricContinuousShiftFactI` removed;
the other hypotheses are unchanged.
-/

universe u

open MeasureTheory

namespace HarmonicBalls

/-- `SmallMetricDiameterLargeMassStmt` (Proposition 11.9) from the hypotheses of `firstPass_11_9_derivedInputs38`
without `hShift`, which is supplied by `lqgMetricContinuousShiftFactI_of_fieldAxioms` from `hAx`. -/
theorem firstPass_11_9_derivedInputsContinuousShift
    (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (h1110 : SmallMetricDiameterLargeMassSquareStmt.{u}) :
    SmallMetricDiameterLargeMassStmt.{u} :=
  firstPass_11_9_derivedInputs38 hMet
    (lqgMetricContinuousShiftFactI_of_fieldAxioms fun Ω _ P γ ξ α₀ hC hcirc => hAx γ ξ α₀ Ω P hC hcirc) hAx h1110

/-- `SmallMetricDiameterLargeMassSquareStmt` (Lemma 11.10) from the hypotheses of
`S11c.firstPass_11_10_derivedInputs38` without `hFactI`, which is supplied by
`lqgMetricContinuousShiftFactI_of_fieldAxioms` from `hAx`. -/
theorem S11c.firstPass_11_10_derivedInputsContinuousShift
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCM : CameronMartinEventTransferFrozen.{u})
    (hPos : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc) :
    SmallMetricDiameterLargeMassSquareStmt.{u} :=
  S11c.firstPass_11_10_derivedInputs38 hDC hCM hPos hSupM hFin
    (lqgMetricContinuousShiftFactI_of_fieldAxioms fun Ω _ P γ ξ α₀ hC hcirc => hAx γ ξ α₀ Ω P hC hcirc) hM1 hAx

end HarmonicBalls
