import HarmonicBalls.FirstPass.S11i.Step8PhysExists
import HarmonicBalls.FirstPass.S11i.InsertionTransfer
import HarmonicBalls.FirstPass.Phase2.CameronMartinReweightingDerived2
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived
import HarmonicBalls.FirstPass.Phase2.NonatomicHolds
import HarmonicBalls.FirstPass.Phase2.LocalDecoderCommonDerived
import HarmonicBalls.FirstPass.Phase2.CoordChangeHolds

/-!
# Insertion transfer at unit scale (proof of Lemma 11.13, Step 8): reduction to the metric inputs

`Step8InsertionTransferK0Stmt` (`S11i/Step8PhysExists.lean:183`) transfers the window frequency of the certificate
events at unit scale from the insertion-zero LQG models to the insertion-`α` models, `α < Q_γ`, uniformly over laws
(universe `0`). It is proved in `allModelsAt_insertion_of_zero_k0` (`S11i/InsertionTransfer.lean:484`) from six binders.
Four of them are now theorems:

* the Cameron-Martin reweighting of the whole-plane GFF, `S11aj.cameronMartinGFFReweighting_derived`;
* the existence of the insertion-zero LQG measure, `lqgMeasureExistence_forall_zero`;
* the absence of atoms of the insertion-`α` LQG measure, `lqgMeasureNonatomic_holds`;
* the local measure kernel, `LocalDecoderCommon.localMeasureKernelStmt_derived`.

So `Step8InsertionTransferK0Stmt` follows from the local metric replacement `LocalMetricReplacementStmt`
(`S11r/LocalMetricReplacement.lean:57`; its unrooted clause is `localMetricReplacement_unrooted_derived`, the rooted
clause is open) and the axioms of the LQG metric of the field `LQGMetricFieldAxiomsUnivFrozen` (Gwynne-Miller,
Section 1.2). With the coordinate change at insertion `α` (`coordChangeAlpha0Stmt_holds`), route 1 of
`Step8PhysExists.lean` then gives the Step 8 identity `Step8IdentityGivenPinchEventCanonicalStmt.{0}` from these two
inputs and the event calibration `Step8EventCalibrationStmt.{0}`.
-/

namespace HarmonicBalls.FirstPassS11iStep8PhysExists

open MeasureTheory

/-- **Insertion transfer at unit scale from the metric inputs.** The window frequency of the certificate events at
unit scale passes from all insertion-zero models to all insertion-`α` models (`α < Q_γ`), given the local metric
replacement and the axioms of the LQG metric of the field. The Cameron-Martin reweighting, the existence of the
insertion-zero LQG measure, the absence of atoms and the local measure kernel are supplied by theorems. -/
theorem step8InsertionTransferK0Stmt_of_metricInputs
    (hR : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (hLF : LQGMetricFieldAxiomsUnivFrozen.{0}) :
    Step8InsertionTransferK0Stmt := by
  intro γ α q δ M U V W T Q' Q hgeom hγ0 hγ2 hα hzero
  exact FirstPassS11iInsertionTransfer.allModelsAt_insertion_of_zero_k0 hgeom hγ0 hγ2 hα
    S11aj.cameronMartinGFFReweighting_derived
    (fun Ω _ P hC hcirc => lqgMeasureExistence_forall_zero γ Ω P hC hcirc)
    (fun Ω _ P hC hcirc => lqgMeasureNonatomic_holds Ω P γ α hC hcirc)
    (fun c₁ c₂ r₁ r₂ => LocalDecoderCommon.localMeasureKernelStmt_derived γ c₁ c₂ r₁ r₂)
    (fun c₁ c₂ r₁ r₂ => hR γ c₁ c₂ r₁ r₂) hLF hzero

/-- **The Step 8 identity at universe `0` from the event calibration and the metric inputs.** Route 1
(`step8Identity_given_pinchEvent_canonical_of_route1`) with the coordinate change at insertion `α` supplied by
`coordChangeAlpha0Stmt_holds` and the unit-scale insertion transfer by `step8InsertionTransferK0Stmt_of_metricInputs`. -/
theorem step8Identity_given_pinchEvent_canonical_of_calibration
    (hCal : Step8EventCalibrationStmt.{0})
    (hR : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (hLF : LQGMetricFieldAxiomsUnivFrozen.{0}) :
    Step8IdentityGivenPinchEventCanonicalStmt.{0} :=
  step8Identity_given_pinchEvent_canonical_of_route1 coordChangeAlpha0Stmt_holds.{0} hCal
    (step8InsertionTransferK0Stmt_of_metricInputs hR hLF)

end HarmonicBalls.FirstPassS11iStep8PhysExists
