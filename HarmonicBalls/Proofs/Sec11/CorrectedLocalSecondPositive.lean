import HarmonicBalls.FirstPass.Phase2.Step8UniformInsertionProved

/-!
# Positive probability of the first two local pinch events

Lemma 11.21 of the corrected paper (`s11-pinch:lem:E2`): for the buffered pinch geometry, the field
`h^α = g - α log |·|` with `α < Q` and every `M > 0`, the local events
`E₁ = {L > A, a₀ > d₀}` and `E₂(M) = {a₁ > d₁, μ(U) > M S}` of equation `s11-pinch:eq:Es`
(`pinchFirstEventLocal`, `pinchSecondEventLocal`) occur simultaneously with positive probability.

The intersection contains, up to a null set, the common local certificate event of
`step8_uniform_source_certificate`, which has positive probability at every admissible insertion.
The first theorem gives a measurable subevent of positive probability; the second states the
positivity of the outer measure of the intersection.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric FirstPassS11i

/-- Lemma 11.21, measurable form: the intersection `E₁ ∩ E₂(M)` of the first two local pinch
events contains a measurable event of positive probability. -/
theorem pinchFirstSecondEventLocal_exists_measurable_pos
    {U V W T Q' Q : Set ℂ} {δ γ ξ α M : ℝ}
    (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hM : 0 < M) (hα : α < lqgQ γ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α hC D) :
    ∃ A ⊆ {ω | pinchFirstEventLocal (D ω) W T Q' Q δ ∧
        pinchSecondEventLocal (μ ω) (D ω) U V δ M},
      MeasurableSet A ∧ 0 < P A := by
  obtain ⟨E, _, _, hPG, _, _, hseed, _⟩ :=
    step8_uniform_source_certificate U V W T Q' Q δ hG γ ξ M hγ0 hγ2 hM
  obtain ⟨hpos, hcert⟩ := hseed α hα Ω P hC hcirc μ D hGFF hμ hD
  have hB : MeasurableSet {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} :=
    (Section6.fieldSigmaAlgebraModConst_le α hC _).trans (hGFF.fieldSigmaAlgebra_le α _) _
      (localModConstField_measurable α hC _ hPG.1)
  set N := toMeasurable P {ω | ¬ (localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E ↔
    CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0)} with hN
  refine ⟨{ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} \ N, ?_,
    hB.diff (measurableSet_toMeasurable _ _), ?_⟩
  · rintro ω ⟨hωE, hωN⟩
    have hiff : localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E ↔
        CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0 := by
      by_contra h
      exact hωN (subset_toMeasurable _ _ h)
    have hrule := (S11i.Step8Calibration.certificateEvent_iff_pinchLocalRule
      (μ ω) (D ω) U V W T Q' Q δ M).mp (hiff.mp hωE)
    exact ⟨hrule.1, hrule.2.1⟩
  · rwa [measure_sdiff_null (by rw [hN, measure_toMeasurable]; exact ae_iff.mp hcert)]

/-- Lemma 11.21: for every `M > 0` the first two local pinch events `E₁` and `E₂(M)` occur
simultaneously with positive probability. -/
theorem pinchFirstSecondEventLocal_pos
    {U V W T Q' Q : Set ℂ} {δ γ ξ α M : ℝ}
    (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hM : 0 < M) (hα : α < lqgQ γ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α hC D) :
    0 < P {ω | pinchFirstEventLocal (D ω) W T Q' Q δ ∧
      pinchSecondEventLocal (μ ω) (D ω) U V δ M} := by
  obtain ⟨A, hA, -, hpos⟩ := pinchFirstSecondEventLocal_exists_measurable_pos hG hγ0 hγ2 hM hα
    P hC hcirc μ D hGFF hμ hD
  exact hpos.trans_le (measure_mono hA)

end HarmonicBalls
