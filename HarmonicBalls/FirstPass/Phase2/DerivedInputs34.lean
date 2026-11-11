import HarmonicBalls.FirstPass.Phase2.DerivedInputs31
import HarmonicBalls.FirstPass.Phase2.InnerMeasurableDerived
import HarmonicBalls.FirstPass.Phase2.CircleAverageLocalityLinkDerived

/-!
# Trade wrapper of the counted result 11.16: inner measurability binders (audit R2, line 40)

`firstPass_11_16_corrected_derivedInputs` (`FirstPass/Phase2/DerivedInputs31.lean:24`) is the counted declaration of
the result 11.16 and has eleven binders. Two of them are inner measurability inputs that have a theorem of their Prop
with no hypothesis:

* `hM : LQGMassInnerMeasurableFrozen` (`FirstPass/Frozen/S11k.lean:65`) is discharged by the binder-free theorem
  `lqgMassInnerMeasurable_derived'` (`FirstPass/Phase2/CircleAverageLocalityLinkDerived.lean:196`).
* `hDiam : LQGInternalDiamInnerMeasurableFrozen` (`FirstPass/Frozen/S11k.lean:87`) is discharged by
  `lqgInternalDiamInnerMeasurable_derived` (`FirstPass/Phase2/InnerMeasurableDerived.lean:78`). Its only binder `hFA`
  is the forall-form of the field axioms, which is the binder `hAx : LQGMetricFieldAxiomsUnivFrozen`
  (`FirstPass/Frozen/S11j.lean:149`) of this wrapper. The order of the forall arguments differs, so `hAx` is
  reordered by a lambda. No Prop is edited.

The binders `hAx`, `hholder`, `hEx`, `hWeyl`, `hNa0`, `hNa`, `hPos`, `hD`, `hMk` keep their types, so the number of
binders decreases from eleven to nine. The counted row of 11.16 binds none of the ledger rows 8, 17, 23 of
`docs/campaign/PHASE2-DERIVATION-STATUS.md`, so this trade does not touch the wrappers of those rows.
-/

open MeasureTheory

universe u

namespace HarmonicBalls

/-- Trade wrapper of `firstPass_11_16_corrected_derivedInputs`: the binders `hM` and `hDiam` are discharged by the
binder-free theorem `lqgMassInnerMeasurable_derived'` and by `lqgInternalDiamInnerMeasurable_derived` applied to the
field axioms `hAx`. The remaining binders are those of `firstPass_11_16_corrected_derivedInputs`, with the same types,
and the conclusion is `PinchSecondEventFaithfulStmt`. -/
theorem firstPass_11_16_corrected_derivedInputs34 (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
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
    (hMk : DomainMarkovConditionalPositiveFrozen.{u}) :
    PinchSecondEventFaithfulStmt.{u} :=
  firstPass_11_16_corrected_derivedInputs hAx hholder hEx hWeyl hNa0 hNa hPos hD
    lqgMassInnerMeasurable_derived'
    (lqgInternalDiamInnerMeasurable_derived fun γ ξ α₀ Ω _ P hC hcirc => hAx Ω P γ ξ α₀ hC hcirc)
    hMk

end HarmonicBalls
