import HarmonicBalls.Proofs.Sec11.PinchActualThresholdSelection
import HarmonicBalls.Proofs.Sec11.PinchActualE3Locality
import HarmonicBalls.Proofs.Sec11.PinchActualJointShiftConsumer

/-! # Positive probability of the third local pinch event -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- For the actual inserted field, positivity of the first two local events
implies positivity of their intersection with the third local event. -/
theorem IsWholePlaneGFF.pinchLocal_three_positive_of_first_two
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {γ ξ α M δ : ℝ} {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    {U V W T Q' Q : Set ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ)
    (hD : IsLQGMetricOfField P γ ξ α hC D)
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hconfig : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hpos : 0 < P {ω | pinchFirstEventLocal (D ω) W T Q' Q δ ∧
      pinchSecondEventLocal (μ ω) (D ω) U V δ M}) :
    0 < P {ω | pinchFirstEventLocal (D ω) W T Q' Q δ ∧
      pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧
      pinchThirdEventLocal (D ω) V W δ} := by
  have hDfield := hD
  obtain ⟨𝔇, h𝔇, _⟩ := hDfield
  have hξ := isLQGMetric_xi_pos γ ξ 𝔇 hγ hγ₂ h𝔇
  obtain ⟨c₁, c₂, hc₁, hc₂, hp⟩ :=
    hh.exists_actual_pinch_third_thresholds hγ hγ₂ hα hD hconfig hpos
  obtain ⟨φ, hφC, hφc, _, _, _, _, htriple⟩ :=
    hgeo.exists_third_shift_local_triple hξ hc₁ hc₂
  let f := S11y.shiftWeight3 ξ (min 1 (c₁ / (2 * c₂))) φ
  have hf : IsTestFunction univ f := by
    refine ⟨?_, S11y.shiftWeight3_hasCompactSupport hφc, subset_univ _⟩
    exact contDiff_const.mul (contDiff_const.mul hφC)
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
    (lqgMetricFieldAxiomsUnivFrozen_derived Ω P γ ξ α hC hcirc) hh hγ hγ₂ hα hD
  have hshift : 0 < P {ω |
      pinchFirstEventLocal (fun x y => (weylScaling (D ω) ξ f x y).toReal) W T Q' Q δ ∧
      pinchSecondEventLocal ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * f z))))
        (fun x y => (weylScaling (D ω) ξ f x y).toReal) U V δ M ∧
      pinchThirdEventLocal (fun x y => (weylScaling (D ω) ξ f x y).toReal) V W δ} := by
    refine hp.trans_le (measure_mono_ae ?_)
    filter_upwards [hmetric] with ω hmetricω hω
    exact htriple (D ω) (μ ω) γ M hmetricω hω.1.1 hω.1.2 hω.2.1 hω.2.2
  exact (hh.pinchLocal_events_smooth_shift_positive_iff_actual hμ hγ hγ₂ hα hD
    hgeo f hf M).mpr hshift

end HarmonicBalls
