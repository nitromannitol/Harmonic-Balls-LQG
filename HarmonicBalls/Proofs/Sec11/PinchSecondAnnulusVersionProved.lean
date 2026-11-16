import HarmonicBalls.FirstPass.S11t
import HarmonicBalls.FirstPass.S11k.BundleParts
import HarmonicBalls.FirstPass.Phase2.CircleAverageLocalityLinkDerived
import HarmonicBalls.FirstPass.Phase2.GreenPotentialHolderHolds
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived
import HarmonicBalls.FirstPass.Phase2.NonatomicHolds
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling

/-!
# Section 11: the exterior version of the annular Green-potential supremum

In the proof of the second pinch event (corrected paper, Lemma `s11-pinch:lem:E2`, event `eq:second-event`), the
annular quantity `SG_{3,6}(0)` is measurable with respect to the field outside `W` and finite. In the repository this
is `BundleParts.PinchSecondAnnulusStep` (`FirstPass/S11k/BundleParts.lean`): for every buffered pinch geometry,
`0 < γ < 2`, `α₀ < Q`, every whole-plane GFF and its LQG measure `μ` with insertion `α₀`, the supremum
`annulusGreenPotentialSup (μ ω) 0 3 6` has a version measurable for the mean-zero field pairings on `(closure W)ᶜ`,
equal to it almost surely and finite almost surely.

The argument is the one of `exists_exterior_annulusGreenPotentialSup_of_buffered_singular`
(`FirstPass/S11p/ExteriorMass.lean`), packaged as `PinchSecondAnnulusS11t.pinchSecondAnnulusStep_of_N2_inputs`:
the LQG mass of open sets in the annulus `𝔸_{3,6}`, which avoids `closure W`, is determined by the field there; the
Green-potential bound of Bou-Rabee–Gwynne Prop. 2.5 gives finiteness for the insertion-free measure `μ₀`, and the
singular density relating `μ` to `μ₀` is bounded on the annulus. Each input of that reduction is a proved theorem:

* `lqgMassInnerMeasurable_derived'` (locality and measurability of the LQG mass);
* `greenPotentialHolderStmt_holds` (the Green-potential bound);
* `lqgMeasureExistence_forall_exponents` (existence of `μ₀` on the same probability space);
* `Section6.lqgMeasureWeylScaling` (Weyl scaling of `μ₀`);
* `lqgMeasureNonatomicAll_holds` (non-atomicity of the LQG measures).

## Main statements

* `BundleParts.pinchSecondAnnulusStep_holds`: `BundleParts.PinchSecondAnnulusStep`, with no hypotheses.
* `BundleParts.exists_exterior_annulusGreenPotentialSup_version`: the same conclusion for fixed data.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

universe u

namespace BundleParts

/-- The annular Green-potential supremum of the LQG measure has a version measurable for the field outside
`closure W`, equal to it and finite almost surely, for every buffered pinch geometry, `0 < γ < 2` and `α₀ < Q`. -/
theorem pinchSecondAnnulusStep_holds : PinchSecondAnnulusStep.{u} :=
  PinchSecondAnnulusS11t.pinchSecondAnnulusStep_of_N2_inputs lqgMassInnerMeasurable_derived'
    greenPotentialHolderStmt_holds
    (fun γ Ω _ P hC hcirc => lqgMeasureExistence_forall_exponents γ 0 Ω P hC hcirc)
    (fun γ Ω _ P hC hcirc => Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc)
    (fun γ Ω _ P hC hcirc => lqgMeasureNonatomicAll_holds γ 0 Ω P hC hcirc)
    (fun γ α₀ Ω _ P hC hcirc => lqgMeasureNonatomicAll_holds γ α₀ Ω P hC hcirc)

/-- `pinchSecondAnnulusStep_holds` for a fixed geometry, exponents and realization. -/
theorem exists_exterior_annulusGreenPotentialSup_version {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hG : IsBufferedPinchGeometry U V W T Q' Q δ) {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∃ G : Ω → ℝ≥0∞,
      Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] G ∧
        (∀ᵐ ω ∂P, G ω = annulusGreenPotentialSup (μ ω) 0 3 6) ∧ ∀ᵐ ω ∂P, G ω ≠ ⊤ :=
  pinchSecondAnnulusStep_holds U V W T Q' Q δ hG γ α₀ hγ0 hγ2 hα Ω P hC hcirc μ hGFF hμ

end BundleParts

end HarmonicBalls
