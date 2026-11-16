import HarmonicBalls.FirstPass.Phase2.Step8UniformInsertionProved

/-! # Positive probability of the first local pinch event -/

universe u

namespace HarmonicBalls

open MeasureTheory Set Metric Filter

/-- The first local pinch event has positive probability for a logarithmically
inserted field at every admissible insertion parameter. -/
theorem pinchFirstEventLocal_pos
    {U V W T Q' Q : Set ℂ} {δ γ ξ α : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (hgff : IsWholePlaneGFF P hC hcirc)
    (hD : IsLQGMetricOfField P γ ξ α hC D) :
    0 < P {ω | pinchFirstEventLocal (D ω) W T Q' Q δ} := by
  obtain ⟨μ, hμ⟩ := lqgMeasureExistence_forall_field Ω P γ α hC hcirc hgff hγ hγ2 hα
  obtain ⟨E, _, _, _, _, _, hseed, _⟩ :=
    step8_uniform_source_certificate U V W T Q' Q δ hgeo γ ξ 1 hγ hγ2 (by norm_num)
  obtain ⟨hpos, hcert⟩ := hseed α hα Ω P hC hcirc μ D hgff hμ hD
  refine hpos.trans_le (measure_mono_ae ?_)
  filter_upwards [hcert] with ω hω hmem
  have hrule := (S11i.Step8Calibration.certificateEvent_iff_pinchLocalRule
    (μ ω) (D ω) U V W T Q' Q δ 1).mp (hω.mp hmem)
  exact hrule.1

end HarmonicBalls
