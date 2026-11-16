import HarmonicBalls.Proofs.GFF.CommonContinuousCircleLQGVersion
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge

/-! # Continuous circle averages of the whole-plane field

A measurable continuous version of the circle averages has the Gaussian law
and covariance of the normalized whole-plane field.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace HarmonicBalls

/-- A measurable continuous circle-average version has the normalized GFF law,
with agreement at all positive circles on one event. -/
theorem IsWholePlaneGFF.exists_measurable_gff_circle_average
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) :
    ∃ H : ℝ → ℂ → Ω → ℝ,
      LQGDimension.IsGFFCircleAverage H P ∧
      (∀ r z, Measurable (H r z)) ∧
      ∀ᵐ ω ∂P, ∀ r, 0 < r → ∀ z, H r z ω = hcirc ω r z := by
  obtain ⟨F, hFm, _, hF⟩ := hh.exists_measurable_continuous_circle_version
  obtain ⟨K, hK, _, hKraw⟩ :=
    LQGMetric.CircleAvg.exists_isGFFCircleAverage_normalized hh.reconstructedGFF_normalized
  have hKactual : ∀ r, 0 < r → ∀ z, K r z =ᵐ[P] fun ω => hcirc ω r z := by
    intro r hr z
    filter_upwards [hKraw r hr z, hh.ae_circleAvg_reconstructedGFF hr z] with ω hk ha
    exact hk.trans ha.symm
  let H : ℝ → ℂ → Ω → ℝ := fun r z ω => circleProfile (F ω) r z
  have heq : ∀ r, 0 < r → ∀ z, H r z =ᵐ[P] K r z := by
    intro r hr z
    simpa only [H, circleProfile, dite_eq_left hr, Function.comp_def, id_eq] using
      (hF (⟨r, hr⟩, z)).trans (hKactual r hr z).symm
  refine ⟨H, ⟨hK.isProbabilityMeasure, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact hK.isGaussianProcess.congr fun p => (heq p.1 p.1.2 p.2).symm
  · intro r hr z
    rw [integral_congr_ae (heq r hr z)]
    exact hK.integral_eq_zero r hr z
  · intro r hr s hs z w
    rw [LQGMetric.CircleAvg.covariance_congr_ae (heq r hr z) (heq s hs w)]
    exact hK.covariance_eq r hr s hs z w
  · intro r hr ω
    simpa only [H, circleProfile, dite_eq_left hr, Function.comp_def, id_eq] using
      (F ω).continuous.comp (continuous_const.prodMk continuous_id)
  · intro r z
    by_cases hr : 0 < r
    · simpa only [H, circleProfile, dite_eq_left hr, Function.comp_def, id_eq] using
        (ContinuousMap.measurable_eval (⟨r, hr⟩, z)).comp hFm
    · simpa only [H, circleProfile, dite_eq_right hr] using
        (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
  · filter_upwards [hh.ae_circle_map_eq_raw hF] with ω hω r hr z
    simpa only [H, circleProfile, dite_eq_left hr] using hω (⟨r, hr⟩, z)

end HarmonicBalls
