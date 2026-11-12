import HarmonicBalls.FirstPass.S11i.Step8CalibrationCanonical

/-!
# Positivity of the scale-one certificate probability at insertion `γ`

Step 8 of Lemma 11.13 (paper, before `eq:dyadic-frequency`) puts `p_γ(M) = P[E₁^{h^γ}(0; M)] > 0`, the probability of the
certificate event at Euclidean radius one about the origin for the field with a `γ`-log singularity at the origin. In this
formalization the certificate event `FirstPassS11i.CertificateEvent` (`S11i/Certificate.lean:42`) is an event of the LQG
measure and metric, while the Lemma 11.12 event `E` is a Borel set of local pairings on `B₇(0)` modulo constants. The proof of
Lemma 11.12 gives more than its statement: `pinchLocalCertificate_canonical_of_inputs` (`S11i/Step8CalibrationCanonical.lean`)
provides an `E` with `PinchEventGammaCanonicalStmt` (in particular positive probability in every insertion-`γ` model) that
agrees almost surely with the scale-one certificate event in every insertion-`γ` model.

* `certificateEvent_prob_pos_of_calibrated`: under these two clauses, the scale-one certificate event has positive
  probability in every insertion-`γ` model, whatever its LQG metric.
-/

universe u

open MeasureTheory Set Metric

namespace HarmonicBalls

/-- **Positivity of the certificate probability at insertion `γ`.** Let `E` be a Lemma 11.12 event at `γ`
(`PinchEventGammaCanonicalStmt`) that agrees almost surely with the scale-one certificate event about `0` in every
insertion-`γ` model (the conclusion of `pinchLocalCertificate_canonical_of_inputs`). Then in every insertion-`γ` model the
certificate event `𝓔₁(0; M)` (`O_* = pinchOmegaGeom W Q δ`, `η = δ`) has positive probability. -/
theorem certificateEvent_prob_pos_of_calibrated {U V W T Q' Q : Set ℂ} {δ γ M : ℝ}
    {E : Set (ModConstTestPairings (ball (0 : ℂ) 7))}
    (hPG : PinchEventGammaCanonicalStmt.{u} U T Q' Q γ M E)
    (hEq : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ → IsLQGMetricOfField P γ (lqgXi γ) γ hC D →
      ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
        FirstPassS11i.CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0))
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ γ hcirc μ)
    (hD : IsLQGMetricOfField P γ (lqgXi γ) γ hC D) :
    0 < P {ω | FirstPassS11i.CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0} := by
  obtain ⟨-, hall⟩ := hPG
  obtain ⟨-, hpos, -⟩ := hall Ω P hC hcirc μ D hG hμ hD
  have hae : {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E} =ᵐ[P]
      {ω | FirstPassS11i.CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0} :=
    (hEq Ω P hC hcirc μ D hG hμ hD).mono fun ω hω => propext hω
  rwa [← measure_congr hae]

end HarmonicBalls
