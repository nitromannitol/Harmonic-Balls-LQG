import HarmonicBalls.FirstPass.Phase2.Step8IdentityUniv
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived

/-!
# Lemma 11.13 (canonical exponent) with the Step 8 identity supplied

The canonical form of Lemma 11.13, `firstPass_11_13_canonical` (`S11i/Corrected11_13.lean:127`), takes four inputs:
the axioms of the LQG metric field `hAx`, the existence of the insertion-`γ` LQG measure `hMeas`, the Lemma 11.12 event
`hPE` (part (c)) and the Step 8 identity `hId` (part (d), `Step8IdentityGivenPinchEventCanonicalStmt`).

Here `hMeas` is the theorem `lqgMeasureExistence_forall_field`, and `hId` is
`step8Identity_given_pinchEvent_canonical_of_calibration_fieldAxioms_univ` (`Phase2/Step8IdentityUniv.lean`), which
needs only the event calibration `Step8EventCalibrationStmt` and the field axioms. So the Step 8 identity is no longer an
input of Lemma 11.13: it is replaced by the event calibration.

* `firstPass_11_13_canonical_derivedInputsCalibration`: inputs `hAx`, `hPE`, `hCal`.
* `closure_11_13_canonical_derivedInputsCalibration`: inputs `hAx`, the corrected Lemma 11.12 `h12` (which gives `hPE`
  through `pinchEventGamma_exists`, as in `Closure.closure_11_13_canonical`), `hCal`.
-/

universe u

open MeasureTheory

namespace HarmonicBalls

/-- `CorrectedLemma11_13CanonicalStmt` from `firstPass_11_13_canonical`, with the existence of the LQG measure supplied
(`lqgMeasureExistence_forall_field`) and the Step 8 identity `hId` derived from the event calibration `hCal` and the
field axioms `hAx` (`step8Identity_given_pinchEvent_canonical_of_calibration_fieldAxioms_univ`). -/
theorem firstPass_11_13_canonical_derivedInputsCalibration
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hPE : Step8PinchEventCanonicalStmt.{u})
    (hCal : FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{u}) :
    CorrectedLemma11_13CanonicalStmt.{u} :=
  firstPass_11_13_canonical (fun γ ξ α₀ Ω _ P hC hcirc => hAx Ω P γ ξ α₀ hC hcirc)
    (fun γ Ω _ P hC hcirc => lqgMeasureExistence_forall_field Ω P γ γ hC hcirc) hPE
    (FirstPassS11iStep8PhysExists.step8Identity_given_pinchEvent_canonical_of_calibration_fieldAxioms_univ hCal hAx)

/-- `CorrectedLemma11_13CanonicalStmt` from the field axioms `hAx`, the corrected Lemma 11.12 `h12` and the event
calibration `hCal`: the Lemma 11.12 event `hPE` at the canonical exponent is `pinchEventGamma_exists` applied to `h12`. -/
theorem closure_11_13_canonical_derivedInputsCalibration
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (h12 : CorrectedLemma11_12Stmt.{u})
    (hCal : FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{u}) :
    CorrectedLemma11_13CanonicalStmt.{u} :=
  firstPass_11_13_canonical_derivedInputsCalibration hAx
    (fun _ _ _ _ _ _ _ hgeo γ _ hγ hγ2 hM => pinchEventGamma_exists (ξ := lqgXi γ) h12 hgeo hγ hγ2 hM) hCal

end HarmonicBalls
