import HarmonicBalls.Proofs.Sec11.PinchOutsideCenterDistance
import HarmonicBalls.Proofs.Sec11.PinchOutsideQDistance
import HarmonicBalls.Proofs.Sec11.PinchOutsideCorridor
import HarmonicBalls.Proofs.Sec11.PinchOutsideDiameter
import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstPositive

/-! # The first pinch certificate as an outside-field event

The local metric and smooth-shift arguments use Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- The open first pinch certificate has an outside-field measurable version
of positive probability for the whole-plane GFF base metric. -/
theorem IsCorrectedPinchConfiguration.exists_positive_outside_first_certificate
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ} (hξ : 0 < ξ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∃ A : Set Ω,
      MeasurableSet[MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ)
        inferInstance] A ∧ 0 < P A ∧
      A =ᵐ[P] {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ} := by
  obtain ⟨a, ha, hae⟩ := h.exists_outside_baseMetric_corridor_crossing hgff 𝔇 h𝔇
  obtain ⟨b, hb, hbe⟩ := h.exists_outside_baseMetric_Q_distance hgff 𝔇 h𝔇
  obtain ⟨c, hc, hce⟩ := h.exists_outside_baseMetric_buffered_diameter hgff 𝔇 h𝔇
  obtain ⟨d, hd, hde⟩ := h.exists_outside_baseMetric_center_distance hgff 𝔇 h𝔇
  let A : Set Ω := {ω | a ω < b ω ∧ c ω < d ω}
  have hA : MeasurableSet[MeasurableSpace.comap
      (localModConstPairings 0 hC (closure W)ᶜ) inferInstance] A :=
    (measurableSet_lt ha hb).inter (measurableSet_lt hc hd)
  have heq : A =ᵐ[P] {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ} := by
    filter_upwards [hae, hbe, hce, hde] with ω haω hbω hcω hdω
    change (a ω < b ω ∧ c ω < d ω) = _
    rw [haω, hbω, hcω, hdω]
    rfl
  refine ⟨A, hA, ?_, heq⟩
  rw [measure_congr heq]
  exact h.positive_open_first hξ P γ hC hcirc 𝔇 h𝔇 hgff

end HarmonicBalls
