import HarmonicBalls.Proofs.GFF.PfefferSourceMetricCoordinates
import HarmonicBalls.Proofs.GFF.PfefferAroundJointMeasurable
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsDerived
import HarmonicBalls.Steps.Sec11.PinchMetricMeasure

/-! # Joint measurability of actual LQG metric observables

Almost everywhere measurable basis infima give a jointly measurable version
of a random Euclidean length metric. This applies to the metric of a shifted
whole-plane Gaussian free field and its unrestricted around observable.
-/

namespace HarmonicBalls

open Set Filter MeasureTheory
open scoped ENNReal

/-- Countably many almost everywhere measurable basis infima determine a
jointly measurable version of a random Euclidean length metric. -/
theorem exists_measurable_joint_of_ae_basis_inf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : Ω → ℂ → ℂ → ℝ}
    (hcoord : ∀ U : TopologicalSpace.countableBasis (ℂ × ℂ),
      AEMeasurable (fun ω => sInf (Set.image (fun p : ℂ × ℂ =>
        ENNReal.ofReal (D ω p.1 p.2)) U.1)) P)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) :
    ∃ G : Ω × (ℂ × ℂ) → ℝ, Measurable G ∧
      ∀ᵐ ω ∂P, ∀ x y, G (ω, (x, y)) = D ω x y := by
  classical
  let : Countable (TopologicalSpace.countableBasis (ℂ × ℂ)) :=
    (TopologicalSpace.countable_countableBasis (ℂ × ℂ)).to_subtype
  let c : TopologicalSpace.countableBasis (ℂ × ℂ) → Ω → ℝ≥0∞ := fun U =>
    (hcoord U).mk _
  have hc : ∀ U, Measurable (c U) := fun U => (hcoord U).measurable_mk
  have hceq : ∀ᵐ ω ∂P, ∀ U, c U ω = sInf (Set.image (fun p : ℂ × ℂ =>
      ENNReal.ofReal (D ω p.1 p.2)) U.1) :=
    ae_all_iff.mpr fun U => (hcoord U).ae_eq_mk.symm
  let H : Ω × (ℂ × ℂ) → ℝ≥0∞ := fun q =>
    ⨆ U : TopologicalSpace.countableBasis (ℂ × ℂ), if q.2 ∈ U.1 then c U q.1 else 0
  have hH : Measurable H := by
    refine Measurable.iSup fun U => Measurable.ite ?_ ((hc U).comp measurable_fst) measurable_const
    exact (TopologicalSpace.isOpen_of_mem_countableBasis U.2).measurableSet.preimage measurable_snd
  refine ⟨fun q => (H q).toReal, hH.ennreal_toReal, ?_⟩
  filter_upwards [hmetric, hceq] with ω hm he x y
  have hn : 0 ≤ D ω x y := by
    have ht := hm.triangle x y x
    rw [hm.self_eq_zero, hm.symm y x] at ht
    linarith
  have heq : H (ω, (x, y)) = ENNReal.ofReal (D ω x y) := by
    rw [ofReal_eq_iSup_basis_inf (isEuclideanLengthMetric_continuous hm).lowerSemicontinuous (x, y)]
    apply iSup_congr
    intro U
    by_cases h : (x, y) ∈ U.1 <;> simp [h, he]
  rw [heq, ENNReal.toReal_ofReal hn]

/-- The actual shifted field metric has a jointly measurable version agreeing
with every distance on one field event. -/
theorem IsLQGMetric.exists_measurable_joint_pfefferField
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) {f : Ω → ℂ → ℝ}
    (hfcont : ∀ ω, Continuous (f ω)) (hfmeas : ∀ z, Measurable fun ω => f ω z) :
    ∃ G : Ω × (ℂ × ℂ) → ℝ, Measurable G ∧
      ∀ᵐ ω ∂P, ∀ x y, G (ω, (x, y)) = 𝔇 (pfefferField hC f ω) x y := by
  apply exists_measurable_joint_of_ae_basis_inf
  · intro U
    exact h𝔇.aemeasurable_pfefferField_sInf hgff hfcont hfmeas U.1
  · exact (h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc f hgff hfcont hfmeas).ae_isEuclideanLengthMetric

/-- The unrestricted around distance is almost everywhere measurable jointly
in the field, center and radii, for any s-finite parameter measure. -/
theorem IsLQGMetric.aemeasurable_pfefferField_around_joint
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) {f : Ω → ℂ → ℝ}
    (hfcont : ∀ ω, Continuous (f ω)) (hfmeas : ∀ z, Measurable fun ω => f ω z)
    (ν : Measure (ℂ × ℝ × ℝ)) [SFinite ν] :
    AEMeasurable (fun q : Ω × (ℂ × ℝ × ℝ) =>
      pfefferAround (𝔇 (pfefferField hC f q.1)) q.2.1 q.2.2.1 q.2.2.2) (P.prod ν) := by
  let : IsProbabilityMeasure P := hgff.isGaussianProcess.isProbabilityMeasure
  obtain ⟨G, hG, hGeq⟩ := h𝔇.exists_measurable_joint_pfefferField hgff hfcont hfmeas
  have hpoint : ∀ x y, AEMeasurable (fun ω => 𝔇 (pfefferField hC f ω) x y) P := by
    intro x y
    apply ((hG.comp (measurable_id.prodMk measurable_const)).aemeasurable).congr
    filter_upwards [hGeq] with ω hω
    exact hω x y
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (pfefferField hC f ω)) :=
    (h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc f hgff hfcont hfmeas).ae_isEuclideanLengthMetric
  exact aemeasurable_pfefferAround_joint_of_ae_pointwise ν
    (D := fun ω => 𝔇 (pfefferField hC f ω)) hpoint hmetric

/-- The around distance of a logarithmically inserted LQG field is almost
 everywhere measurable jointly in the field, center and radii. -/
theorem IsWholePlaneGFF.aemeasurable_singular_pfefferAround_joint
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (ν : Measure (ℂ × ℝ × ℝ)) [SFinite ν] :
    AEMeasurable (fun q : Ω × (ℂ × ℝ × ℝ) =>
      pfefferAround (D q.1) q.2.1 q.2.2.1 q.2.2.2) (P.prod ν) := by
  let : IsProbabilityMeasure P := hgff.isGaussianProcess.isProbabilityMeasure
  have haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc :=
    lqgMetricFieldAxiomsUnivFrozen_derived Ω P γ ξ α₀ hC hcirc
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms
    P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD
  obtain ⟨D', hD', heq⟩ :=
    exists_measurable_metric_modification_of_metricFieldAxioms haxioms hgff hγ hγ₂ hα hD
  have hpoint : ∀ x y, AEMeasurable (fun ω => D ω x y) P := by
    intro x y
    apply (hD' x y).aemeasurable.congr
    filter_upwards [heq] with ω hω
    rw [hω]
  exact aemeasurable_pfefferAround_joint_of_ae_pointwise ν hpoint hmetric

end HarmonicBalls
