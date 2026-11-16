import HarmonicBalls.Steps.Sec11.PinchThirdThresholds
import HarmonicBalls.Proofs.Sec11.CorrectedLocalThirdPositive
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsDerived

/-! # Threshold selection for the third local pinch event -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- Positive probability of the first two local events yields deterministic
positive bounds for the actual third crossing distance and closed-piece diameter. -/
theorem IsWholePlaneGFF.exists_actual_pinch_third_thresholds
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {γ ξ α M δ : ℝ} {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    {U V W T Q' Q : Set ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α hC D)
    (hconfig : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hpos : 0 < P {ω | pinchFirstEventLocal (D ω) W T Q' Q δ ∧
      pinchSecondEventLocal (μ ω) (D ω) U V δ M}) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      0 < P {ω | (pinchFirstEventLocal (D ω) W T Q' Q δ ∧
          pinchSecondEventLocal (μ ω) (D ω) U V δ M) ∧
        c₁ ≤ setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)) ∧
        internalDiam (D ω) δ (closure (thickening (3 * δ) W \ V)) ≤ ENNReal.ofReal c₂} := by
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
    (lqgMetricFieldAxiomsUnivFrozen_derived Ω P γ ξ α hC hcirc) hh hγ hγ₂ hα hD
  obtain ⟨n, m, hn, hp⟩ := hconfig.exists_positive_measure_third_thresholds P
    {ω | pinchFirstEventLocal (D ω) W T Q' Q δ ∧
      pinchSecondEventLocal (μ ω) (D ω) U V δ M} D hpos hmetric
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  let G : Set Ω := {ω | IsEuclideanLengthMetric (D ω)}
  have heq : {ω | (pinchFirstEventLocal (D ω) W T Q' Q δ ∧
      pinchSecondEventLocal (μ ω) (D ω) U V δ M) ∧
      (n : ℝ≥0∞)⁻¹ < ENNReal.ofReal (setDist (D ω)
        (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) ∧
      internalDiam (D ω) δ (thickening (3 * δ) W \ V) < (m : ℝ≥0∞)} =ᵐ[P]
      {ω | (pinchFirstEventLocal (D ω) W T Q' Q δ ∧
      pinchSecondEventLocal (μ ω) (D ω) U V δ M) ∧
      (n : ℝ≥0∞)⁻¹ < ENNReal.ofReal (setDist (D ω)
        (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) ∧
      internalDiam (D ω) δ (thickening (3 * δ) W \ V) < (m : ℝ≥0∞)} ∩ G := by
    filter_upwards [hmetric] with ω hω
    simp [G, hω]
  have hpG : 0 < P ({ω | (pinchFirstEventLocal (D ω) W T Q' Q δ ∧
      pinchSecondEventLocal (μ ω) (D ω) U V δ M) ∧
      (n : ℝ≥0∞)⁻¹ < ENNReal.ofReal (setDist (D ω)
        (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) ∧
      internalDiam (D ω) δ (thickening (3 * δ) W \ V) < (m : ℝ≥0∞)} ∩ G) := by
    rwa [← measure_congr heq]
  refine ⟨(n : ℝ)⁻¹, (m : ℝ) + 1, inv_pos.mpr hnreal, by positivity,
    hpG.trans_le (measure_mono ?_)⟩
  intro ω hω
  refine ⟨hω.1.1, ?_, ?_⟩
  · have ht : ENNReal.ofReal ((n : ℝ)⁻¹) ≤ ENNReal.ofReal
        (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) := by
      simpa only [ENNReal.ofReal_inv_of_pos hnreal, ENNReal.ofReal_natCast] using hω.1.2.1.le
    rcases ENNReal.ofReal_le_ofReal_iff'.mp ht with ht | ht
    · exact ht
    · exact ((not_le_of_gt (inv_pos.mpr hnreal)) ht).elim
  · rw [hω.2.internalDiam_closure_eq hconfig.δ₀_mem.1]
    calc
      internalDiam (D ω) δ (thickening (3 * δ) W \ V) ≤ (m : ℝ≥0∞) := hω.1.2.2.le
      _ ≤ ENNReal.ofReal ((m : ℝ) + 1) := by
        simpa only [ENNReal.ofReal_natCast] using
          ENNReal.ofReal_le_ofReal (show (m : ℝ) ≤ (m : ℝ) + 1 by linarith)

end HarmonicBalls
