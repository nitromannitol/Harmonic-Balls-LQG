import HarmonicBalls.FirstPass.Phase2.SquarePositiveHolds
import HarmonicBalls.FirstPass.Phase2.DerivedInputs42
import HarmonicBalls.FirstPass.Phase2.DerivedInputs43
import HarmonicBalls.FirstPass.Phase2.WeylLogTruncationDerivedInputs
import HarmonicBalls.FirstPass.Phase2.NonatomicHolds

/-!
# Counted forms of Lemma 11.10 (closed squares) and Proposition 11.16 with the proved LQG inputs supplied

* `HarmonicBalls.S11c.firstPass_11_10_derivedInputsSquarePositive`: the closed-square form of Lemma 11.10
  (`firstPass_11_10_derivedInputs42`) with the positivity of the LQG mass of closed dyadic squares
  (`lqgMeasureSquarePositiveFrozen_holds`) and the Cameron-Martin event transfer supplied; the latter follows from the
  field axioms of the LQG metric, which the form binds already (`cameronMartinEventTransfer_of_fieldAxioms`).
  Binders 5 → 3: `hDC`, `hFin`, `hAx`.
* `HarmonicBalls.firstPass_11_16_corrected_derivedInputsNonatomic`: Proposition 11.16
  (`firstPass_11_16_corrected_derivedInputs43`) with the non-atomicity of the LQG measure supplied
  (`lqgMeasureNonatomic_holds`, at `α₀ = 0` and at every `α₀`). Binders 5 → 3: `hAx`, `hholder`, `hD`.
-/

open MeasureTheory

universe u

namespace HarmonicBalls.S11c

/-- Lemma 11.10, closed-square form, from the hypotheses `hDC`, `hFin`, `hAx` of `firstPass_11_10_derivedInputs42`:
`hPos` is `lqgMeasureSquarePositiveFrozen_holds` and `hCM` follows from `hAx`. -/
theorem firstPass_11_10_derivedInputsSquarePositive
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc) :
    SmallMetricDiameterLargeMassSquareStmt.{u} :=
  firstPass_11_10_derivedInputs42 (hDC := hDC)
    (hCM := HarmonicBalls.cameronMartinEventTransfer_of_fieldAxioms
      (fun Ω _ P γ ξ α₀ hC hcirc => hAx γ ξ α₀ Ω P hC hcirc))
    (hPos := HarmonicBalls.lqgMeasureSquarePositiveFrozen_holds.{u}) (hFin := hFin) (hAx := hAx)

end HarmonicBalls.S11c

namespace HarmonicBalls

/-- Proposition 11.16 from the hypotheses `hAx`, `hholder`, `hD` of `firstPass_11_16_corrected_derivedInputs43`:
`hNa0` and `hNa` are `lqgMeasureNonatomic_holds`. -/
theorem firstPass_11_16_corrected_derivedInputsNonatomic
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hD : SmallMetricDiameterLargeMassStmt.{u}) :
    PinchSecondEventFaithfulStmt.{u} :=
  firstPass_11_16_corrected_derivedInputs43 (hAx := hAx) (hholder := hholder)
    (hNa0 := fun γ Ω _ P hC hcirc => lqgMeasureNonatomic_holds.{u} Ω P γ 0 hC hcirc)
    (hNa := fun γ α₀ Ω _ P hC hcirc => lqgMeasureNonatomic_holds.{u} Ω P γ α₀ hC hcirc) (hD := hD)

end HarmonicBalls
