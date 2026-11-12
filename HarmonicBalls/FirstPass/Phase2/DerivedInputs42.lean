import HarmonicBalls.FirstPass.Phase2.DerivedInputs41
import HarmonicBalls.FirstPass.Phase2.NonatomicHolds
import HarmonicBalls.FirstPass.Phase2.WeylShiftedChainDerived

/-!
# Derived-input forms, round 42: unused hypotheses removed

Each theorem below has the conclusion of the declaration named in its docstring and a subset of its hypotheses:
the conclusion already follows from that subset by theorems of this repository. The kept hypotheses are
unchanged; the proofs are chains of applications.

Generated from the types of the wrapped declarations; do not edit by hand.
-/

universe u

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls.Closure

/-- `OriginManyGoodScalesStmt` from the hypotheses `hholder`, `hDG` of `closure_8_3_derivedInputs41` alone:
the hypothesis `hN` of that declaration is not used. -/
theorem closure_8_3_derivedInputs42
    (hholder : GreenPotentialHolderStmt.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds.{u} P γ hC hcirc) :
    OriginManyGoodScalesStmt.{u} := by
  have d1 := HarmonicBalls.lqgMeasureNonatomic_holds.{u}
  exact HarmonicBalls.Closure.closure_8_3_derivedInputs41.{u} (hholder := hholder) (hDG := hDG) (hN := d1)

end HarmonicBalls.Closure

namespace HarmonicBalls.S11c

/-- `SmallMetricDiameterLargeMassSquareStmt` from the hypotheses `hDC`, `hCM`, `hPos`, `hFin`, `hAx` of `firstPass_11_10_derivedInputs41` alone:
the hypothesis `hM1` of that declaration is not used. -/
theorem firstPass_11_10_derivedInputs42
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCM : CameronMartinEventTransferFrozen.{u})
    (hPos : LQGMeasureSquarePositiveFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc) :
    SmallMetricDiameterLargeMassSquareStmt.{u} := by
  exact HarmonicBalls.S11c.firstPass_11_10_derivedInputsWeylShiftedSup.{u} (hDC := hDC) (hCM := hCM) (hPos := hPos) (hFin := hFin) (hAx := hAx)

end HarmonicBalls.S11c
