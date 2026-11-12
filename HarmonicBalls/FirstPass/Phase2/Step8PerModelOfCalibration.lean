import HarmonicBalls.FirstPass.Phase2.Step8PerModelFrequency
import HarmonicBalls.FirstPass.Phase2.DerivedInputsStep8Calibration
import HarmonicBalls.FirstPass.S11i.GammaModel
import HarmonicBalls.FirstPass.S11i.Step8Event

/-!
# The per-model certificate frequency follows from the Step 8 identity

`Step8CertificateFrequencyPerModelStmt` (`Phase2/Step8PerModelFrequency.lean`) is a consequence of the earlier inputs of
Lemma 11.13 (canonical exponent):

* `step8CertificateFrequencyPerModel_of_identity`: from the field axioms `hAx`, the Lemma 11.12 event `hPE` and the
  Step 8 identity `hId` (`Step8IdentityGivenPinchEventCanonicalStmt`). The limit is the canonical probability `q` of the
  Lemma 11.12 event at the insertion `γ`; it is positive because the given model, with its field, carries an
  insertion-`γ` measure and metric (`gammaModel_of_alpha0Model`), in which the event has positive probability.
* `step8CertificateFrequencyPerModel_of_calibration`: from `hAx`, the corrected Lemma 11.12 `h12` and the event
  calibration `hCal` (`Step8EventCalibrationStmt`).

So the input `hPM` of `firstPass_11_13_canonical_of_perModelFrequency` is no stronger than the inputs it replaces.
-/

universe u

open MeasureTheory

namespace HarmonicBalls

/-- **The per-model certificate frequency from the Step 8 identity.** -/
theorem step8CertificateFrequencyPerModel_of_identity (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hPE : Step8PinchEventCanonicalStmt.{u}) (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u}) :
    Step8CertificateFrequencyPerModelStmt.{u} := by
  intro U V W T Q' Q δ₀ hgeom γ α₀ M hγ0 hγ2 hα hM Ω _ P hC hcirc μ D hG hμ hD
  obtain ⟨E, ⟨-, hW⟩, q, hqeq, hfreq⟩ :=
    hId U V W T Q' Q δ₀ hgeom γ α₀ M hγ0 hγ2 hα hM (hPE U V W T Q' Q δ₀ hgeom γ M hγ0 hγ2 hM)
  obtain ⟨μg, Dg, hμg, hDg⟩ :=
    FirstPassS11iGamma.gammaModel_of_alpha0Model (fun γ ξ α₀ Ω _ P hC hcirc => hAx Ω P γ ξ α₀ hC hcirc)
      (fun γ Ω _ P hC hcirc => lqgMeasureExistence_forall_field Ω P γ γ hC hcirc) hγ0 hγ2 Ω P hC hcirc hG D hD
  have : IsProbabilityMeasure P := FirstPassS11af.isProbabilityMeasure_of_isWholePlaneGFF hG
  obtain ⟨-, hpos, -⟩ := hW Ω P hC hcirc μg Dg hG hμg hDg
  have hq : 0 < q := by
    rw [← hqeq Ω P hC hcirc μg Dg hG hμg hDg]
    exact ENNReal.toReal_pos hpos.ne' (measure_ne_top P _)
  obtain ⟨μk, Dk, hsc, hstep⟩ := hfreq Ω P hC hcirc μ D hG hμ hD
  exact ⟨q, hq, μk, Dk, hsc, hstep⟩

/-- **The per-model certificate frequency from the event calibration.** `hPE` is `pinchEventGamma_exists` applied to the
corrected Lemma 11.12 `h12`, and `hId` is `step8Identity_given_pinchEvent_canonical_of_calibration_fieldAxioms_univ`. -/
theorem step8CertificateFrequencyPerModel_of_calibration (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (h12 : CorrectedLemma11_12Stmt.{u})
    (hCal : FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{u}) :
    Step8CertificateFrequencyPerModelStmt.{u} :=
  step8CertificateFrequencyPerModel_of_identity hAx
    (fun _ _ _ _ _ _ _ hgeo γ _ hγ hγ2 hM => pinchEventGamma_exists (ξ := lqgXi γ) h12 hgeo hγ hγ2 hM)
    (FirstPassS11iStep8PhysExists.step8Identity_given_pinchEvent_canonical_of_calibration_fieldAxioms_univ hCal hAx)

end HarmonicBalls
