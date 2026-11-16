import HarmonicBalls.FirstPass.S11an
import HarmonicBalls.FirstPass.S11ap
import HarmonicBalls.FirstPass.S11ad.ExteriorE1
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsConsequencesDerived
import HarmonicBalls.FirstPass.Phase2.CameronMartinReweightingDerived2
import HarmonicBalls.FirstPass.Phase2.DerivedInputs9
import HarmonicBalls.FirstPass.Phase2.WeylScalingCompositionDerived
import HarmonicBalls.FirstPass.Phase2.LQGMetricXiPos

/-! # Positivity of the first local pinch event -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- The first local pinch event has positive probability for the inserted metric. -/
theorem IsWholePlaneGFF.pinchLocal_first_positive_by_shift
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {γ ξ α δ : ℝ} {D : Ω → ℂ → ℂ → ℝ} {U V W T Q' Q : Set ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α hC D)
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    0 < P {ω | pinchFirstEventLocal (D ω) W T Q' Q δ} := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hDfield := hD
  obtain ⟨𝔇, h𝔇, _⟩ := hDfield
  have hξ := isLQGMetric_xi_pos γ ξ 𝔇 hγ hγ₂ h𝔇
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
    (lqgMetricFieldAxiomsUnivFrozen_derived Ω P γ ξ α hC hcirc) hh hγ hγ₂ hα hD
  obtain ⟨b, bQ, hb, hbQ, φQ, φ0, hφQ, hφQc, hφQ1, hφQ0, hφQI,
    hφ0, hφ0c, hφ01, hφ00, hφ0I, hf, hfc, hf0, hpos⟩ :=
    S11ad.exists_E1_shift_pos hgeo (FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom hgeo)
      D hmetric hξ
  have hrule := S11ae.metricEventCertificate_firstLocal (ξ := ξ) hgeo hγ hγ₂
    lqgInternalMetricWeylAeMeasurableFrozen_derived lqgMetricFieldAxiomsUnivFrozen_derived
  have hshift := S11an.hE1shift_of_frozen S11aj.cameronMartinGFFReweighting_derived
    DerivedInputs9.cameronMartinGFFMutualAbsCont_derived weylScalingCompositionFrozen_holds
    lqgMetricFieldAxiomsUnivFrozen_derived hrule hgeo hγ hγ₂ hξ α hα P hC hcirc D hh hD
  obtain ⟨A, hAsub, _, hAp⟩ := metric_event_transfer_of_rule
    DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hrule P hC hcirc hh α hα D hD
    (shiftWeight ξ b bQ φQ φ0) hf hfc hf0 _
    (hshift _ ⟨b, bQ, hb, hbQ, φQ, φ0, hφQ, hφQc, hφQ1, hφQ0, hφQI,
      hφ0, hφ0c, hφ01, hφ00, hφ0I, rfl⟩) hpos
  exact hAp.trans_le (measure_mono hAsub)

/-- The first local event admits a positive-probability representative measurable
with respect to the field outside the buffered disk. -/
theorem IsWholePlaneGFF.exists_positive_outside_pinchLocal_first
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {γ ξ α δ : ℝ} {D : Ω → ℂ → ℂ → ℝ} {U V W T Q' Q : Set ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α hC D)
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ∃ A : Set Ω,
      MeasurableSet[MeasurableSpace.comap (localModConstPairings α hC (closure W)ᶜ)
        inferInstance] A ∧ 0 < P A ∧
      A =ᵐ[P] {ω | pinchFirstEventLocal (D ω) W T Q' Q δ} := by
  obtain ⟨A, hA, hAe⟩ := S11ad.pinchFirstEventLocal_exterior_version
    lqgMetricFieldAxiomsUnivFrozen_derived
    U V W T Q' Q δ hgeo γ ξ α hγ hγ₂ hα Ω P hC hcirc D hh hD
    (FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom hgeo)
  have heq : A =ᵐ[P] {ω | pinchFirstEventLocal (D ω) W T Q' Q δ} := by
    filter_upwards [hAe] with ω hω
    exact propext hω
  refine ⟨A, hA, ?_, heq⟩
  rw [measure_congr heq]
  exact hh.pinchLocal_first_positive_by_shift hγ hγ₂ hα hD hgeo

/-- The crossing distance between the two small circles has an almost surely
positive representative measurable outside the buffered disk. -/
theorem IsWholePlaneGFF.exists_positive_outside_pinchLocal_crossing
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {γ ξ α δ : ℝ} {D : Ω → ℂ → ℂ → ℝ} {U V W T Q' Q : Set ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α hC D)
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ∃ a : Ω → ℝ,
      Measurable[MeasurableSpace.comap (localModConstPairings α hC (closure W)ᶜ)
        inferInstance] a ∧
      (∀ᵐ ω ∂P, a ω = setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ))) ∧
      ∀ᵐ ω ∂P, 0 < a ω := by
  have hE : IsOpen (closure W)ᶜ := isClosed_closure.isOpen_compl
  have hsph : sphere (0 : ℂ) 1 ⊆ (closure W)ᶜ := by
    intro z hz hzW
    have h := BundleParts.closure_W_norm_gt_one hgeo hzW
    rw [mem_sphere_zero_iff_norm] at hz
    linarith
  have hBE : ball (0 : ℂ) (3 * δ) ⊆ (closure W)ᶜ := by
    intro z hz hzW
    have h := BundleParts.closure_W_norm_gt_one hgeo hzW
    rw [mem_ball_zero_iff] at hz
    linarith [hgeo.delta_lt]
  obtain ⟨hmetric, hloc⟩ := S11ad.metric_locality_of_frozen
    lqgMetricFieldAxiomsUnivFrozen_derived γ ξ α hγ hγ₂ hα Ω P hC hcirc D hh hD
  obtain ⟨a, ha, hae⟩ := ExteriorDistances.exists_exterior_setDist_spheres hh α hE hsph hmetric
    (fun V' hV' _ => hloc V' hV') hgeo.delta_pos hBE
  refine ⟨a, ha, hae, ?_⟩
  filter_upwards [hae, hmetric] with ω hω hm
  rw [hω]
  exact IsEuclideanLengthMetric.setDist_spheres_pos hm 0 hgeo.delta_pos (by linarith [hgeo.delta_pos])

end HarmonicBalls
