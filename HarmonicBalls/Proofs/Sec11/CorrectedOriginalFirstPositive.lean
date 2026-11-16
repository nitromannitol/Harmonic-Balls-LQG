import HarmonicBalls.FirstPass.Phase2.Step8UniformInsertionProved
import HarmonicBalls.FirstPass.S11h.LocalEvents
import HarmonicBalls.FirstPass.S11h.Faithful

/-!
# Positive probability of the first original pinch event

Lemma 11.15 of the corrected paper (`lemma:first-event-proof`): for the buffered pinch geometry and
the field `h^α = g - α log |·|` with `α < Q`, the event `Ẽ₁` (`eq:first-event`), formalized as
`pinchFirstEvent`, contains a measurable event of positive probability.

The proof follows the corrected paper: the local event `E₁ = {L > A, a₀ > d₀}` of
`s11-pinch:eq:Es` (`pinchFirstEventLocal`) implies `Ẽ₁` (`pinchFirstEventLocal_subset`, which uses
`D ≥ 0`, an almost sure property of the metric), and up to a null set `E₁` contains the local
certificate event of `step8_uniform_source_certificate`, a measurable event of positive probability
at every admissible insertion. The LQG measure entering the certificate is supplied by
`lqgMeasureExistence_forall_field`.

## Main results

* `pinchFirstEventLocal_exists_measurable_pos`: `E₁` contains a measurable event of positive
  probability.
* `pinchFirstEvent_exists_measurable_pos`: `Ẽ₁` contains a measurable event of positive probability.
* `pinchFirstEventFaithfulStmt_holds`: the corrected statement `PinchFirstEventFaithfulStmt`.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Set Metric FirstPassS11i

/-- The first local pinch event `E₁` contains a measurable event of positive probability, for a
logarithmically inserted field at every admissible insertion parameter. -/
theorem pinchFirstEventLocal_exists_measurable_pos
    {U V W T Q' Q : Set ℂ} {δ γ ξ α : ℝ}
    (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hD : IsLQGMetricOfField P γ ξ α hC D) :
    ∃ A ⊆ {ω | pinchFirstEventLocal (D ω) W T Q' Q δ}, MeasurableSet A ∧ 0 < P A := by
  obtain ⟨μ, hμ⟩ := lqgMeasureExistence_forall_field Ω P γ α hC hcirc hGFF hγ0 hγ2 hα
  obtain ⟨E, _, _, hPG, _, _, hseed, _⟩ :=
    step8_uniform_source_certificate U V W T Q' Q δ hG γ ξ 1 hγ0 hγ2 one_pos
  obtain ⟨hpos, hcert⟩ := hseed α hα Ω P hC hcirc μ D hGFF hμ hD
  have hB : MeasurableSet {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} :=
    (Section6.fieldSigmaAlgebraModConst_le α hC _).trans (hGFF.fieldSigmaAlgebra_le α _) _
      (localModConstField_measurable α hC _ hPG.1)
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hcert)
  refine ⟨{ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} \ N, fun ω hω => ?_,
    hB.diff hNm, by rwa [measure_sdiff_null hN0]⟩
  have hiff : localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E ↔
      CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ 1 1 0 :=
    by_contra fun h => hω.2 (hsub h)
  exact ((S11i.Step8Calibration.certificateEvent_iff_pinchLocalRule
    (μ ω) (D ω) U V W T Q' Q δ 1).mp (hiff.mp hω.1)).1

/-- Lemma 11.15, measurable form: the first original pinch event `Ẽ₁` contains a measurable event
of positive probability. -/
theorem pinchFirstEvent_exists_measurable_pos
    {U V W T Q' Q : Set ℂ} {δ γ ξ α : ℝ}
    (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hD : IsLQGMetricOfField P γ ξ α hC D) :
    ∃ A ⊆ {ω | pinchFirstEvent (D ω) W T Q' Q δ}, MeasurableSet A ∧ 0 < P A := by
  obtain ⟨A, hA, hAm, hpos⟩ :=
    pinchFirstEventLocal_exists_measurable_pos hG hγ0 hγ2 hα P hC hcirc D hGFF hD
  obtain ⟨_, -, hae⟩ := hD
  obtain ⟨N, hsub, hNm, hN0⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp (hae.mono fun ω h u v => (h u v).1))
  refine ⟨A \ N, fun ω hω => ?_, hAm.diff hNm, by rwa [measure_sdiff_null hN0]⟩
  exact pinchFirstEventLocal_subset (D ω) (by_contra fun h => hω.2 (hsub h)) W T Q' Q δ
    (hA hω.1)

/-- Lemma 11.15, corrected form (`PinchFirstEventFaithfulStmt`): for every buffered geometry,
every `γ ∈ (0, 2)`, every `α₀ < Q` and every LQG metric of the field, `P[Ẽ₁] > 0`
(inner-measure form). -/
theorem pinchFirstEventFaithfulStmt_holds : PinchFirstEventFaithfulStmt.{u} := by
  intro U V W T Q' Q δ hG γ α₀ ξ hγ hγ₂ hα Ω _ P hC hcirc D hGFF hD
  exact pinchFirstEvent_exists_measurable_pos hG hγ hγ₂ hα P hC hcirc D hGFF hD

end HarmonicBalls
