import HarmonicBalls.FirstPass.S11k.FirstLExterior
import HarmonicBalls.FirstPass.Phase2.InternalMetricClosedDerived

/-!
# Trade wrapper of the counted result 11.16 with row 39 derived

`firstPass_11_16_corrected` (`FirstPass/S11k/FirstLExterior.lean:260`) binds the frozen closed-domain identity
`InternalMetricClosedEqIInfThickeningFrozen` (`FirstPass/Frozen/S11g.lean:126`, ledger row 39). That identity is
derived with no hypothesis by `internalMetricClosedEqIInfThickening_derived`
(`FirstPass/Phase2/InternalMetricClosedDerived.lean:408`). The wrapper `firstPass_11_16_corrected_derivedInputs`
discharges `hK1` by this binder-free theorem and keeps the other eleven binders of `firstPass_11_16_corrected` with
the same types, so the number of binders decreases from twelve to eleven. No Prop is edited.
-/

open MeasureTheory

universe u

namespace HarmonicBalls

/-- Trade wrapper of `firstPass_11_16_corrected`: the frozen binder `hK1` is discharged by the binder-free theorem
`internalMetricClosedEqIInfThickening_derived` (closed-set exhaustion of the internal metric). The remaining binders
are those of `firstPass_11_16_corrected`, with the same types. -/
theorem firstPass_11_16_corrected_derivedInputs (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hEx : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hWeyl : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hNa0 : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ 0 hC hcirc)
    (hNa : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hPos : PinchFirstEventFaithfulStmt.{u}) (hD : SmallMetricDiameterLargeMassStmt.{u})
    (hM : LQGMassInnerMeasurableFrozen.{u}) (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u}) :
    PinchSecondEventFaithfulStmt.{u} :=
  firstPass_11_16_corrected hAx internalMetricClosedEqIInfThickening_derived hholder hEx hWeyl hNa0 hNa hPos hD hM
    hDiam hMk

end HarmonicBalls
