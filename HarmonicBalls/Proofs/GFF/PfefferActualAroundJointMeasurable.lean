import HarmonicBalls.Proofs.GFF.PfefferSourceMetricCoordinates
import HarmonicBalls.Proofs.GFF.PfefferAroundJointMeasurable
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsDerived
import HarmonicBalls.Steps.Sec11.PinchMetricMeasure
import HarmonicBalls.FirstPass.Phase2.WeylShiftedChainDerived
import HarmonicBalls.FirstPass.Phase2.WeylContinuousShiftDerived

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

/-- A compactly supported deterministic shift of a singular-field metric has
almost everywhere measurable point distances. -/
theorem IsWholePlaneGFF.aemeasurable_singular_weyl_point
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (x y : ℂ) :
    AEMeasurable (fun ω => (weylScaling (D ω) ξ f x y).toReal) P := by
  have haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc :=
    lqgMetricFieldAxiomsUnivFrozen_derived Ω P γ ξ α₀ hC hcirc
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms
    P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD
  have hshift : ∀ᵐ ω ∂P, IsEuclideanLengthMetric
      (fun a b => (weylScaling (D ω) ξ f a b).toReal) := by
    filter_upwards [hmetric] with ω hm
    exact (hm.weylScaling_continuous_isEuclideanLengthMetric ξ hf).2
  obtain ⟨K, hK⟩ := exists_const_mul_le_of_hasCompactSupport hf hfc ξ
  have hg := uniformContinuous_const_mul_of_hasCompactSupport hf hfc ξ
  have hopen := LatticeProb.LQG.aemeasurable_internalMetric_weylScaling
    (D := D) (E := fun ω a b => (weylScaling (D ω) ξ f a b).toReal)
    hf hK hg isOpen_univ
    (fun a b _ _ => aemeasurable_internalMetric_of_fieldAxioms
      lqgMetricFieldAxiomsUnivFrozen_derived hγ hγ₂ hα hgff hD
      (Metric.isOpen_ball.inter isOpen_univ) a b)
    (by filter_upwards [hmetric] with ω hm; exact (LPBridge.isEuclideanLengthMetric_iff _).1 hm)
    (by filter_upwards [hshift] with ω hm; exact (LPBridge.isEuclideanLengthMetric_iff _).1 hm)
    (Eventually.of_forall fun _ _ _ => ENNReal.toReal_nonneg)
    (by
      filter_upwards [hmetric] with ω hm
      intro a b
      exact ENNReal.ofReal_toReal ((hm.weylScaling_continuous_isEuclideanLengthMetric ξ hf).1 a b).ne)
    x y
  have hpoint : AEMeasurable (fun ω => ENNReal.ofReal
      ((weylScaling (D ω) ξ f x y).toReal)) P := by
    apply hopen.congr
    filter_upwards [hshift] with ω hm
    exact (hm.ofReal_eq_internalMetric x y).symm
  simpa using hpoint.ennreal_toReal

/-- A measurable index can select from countably many almost everywhere
measurable functions. -/
theorem aemeasurable_nat_select {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {β : Type*} [MeasurableSpace β] {N : Ω → ℕ} (hN : Measurable N) {g : ℕ → Ω → β}
    (hg : ∀ n, AEMeasurable (g n) P) :
    AEMeasurable (fun ω => g (N ω) ω) P := by
  classical
  let m : ℕ → Ω → β := fun n => (hg n).mk (g n)
  have hm : ∀ n, Measurable (m n) := fun n => (hg n).measurable_mk
  have he : ∀ᵐ ω ∂P, ∀ n, m n ω = g n ω :=
    ae_all_iff.mpr fun n => (hg n).ae_eq_mk.symm
  have hs : Measurable (fun ω => m (N ω) ω) := by
    intro s hs
    have heq : (fun ω => m (N ω) ω) ⁻¹' s =
        ⋃ n, ({ω | N ω = n} ∩ (m n) ⁻¹' s) := by
      ext ω
      simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun h => ⟨N ω, rfl, h⟩, fun ⟨n, hn, h⟩ => hn ▸ h⟩
    rw [heq]
    exact MeasurableSet.iUnion fun n => (measurableSet_eq_fun hN measurable_const).inter (hm n hs)
  exact hs.aemeasurable.congr (by filter_upwards [he] with ω hω; exact hω (N ω))

/-- A continuous Weyl shift of a singular-field metric is almost surely a
Euclidean length metric. -/
theorem IsWholePlaneGFF.ae_singular_weyl_metric
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) {f : ℂ → ℝ} (hf : Continuous f) :
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric
      (fun x y => (weylScaling (D ω) ξ f x y).toReal) := by
  have haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc :=
    lqgMetricFieldAxiomsUnivFrozen_derived Ω P γ ξ α₀ hC hcirc
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms
    P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD
  filter_upwards [hmetric] with ω hm
  exact (hm.weylScaling_continuous_isEuclideanLengthMetric ξ hf).2

/-- A compactly supported continuous shift of a singular-field metric has an
almost everywhere measurable joint around distance. -/
theorem IsWholePlaneGFF.aemeasurable_singular_weyl_around_joint
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (ν : Measure (ℂ × ℝ × ℝ)) [SFinite ν] :
    AEMeasurable (fun q : Ω × (ℂ × ℝ × ℝ) =>
      pfefferAround (fun x y => (weylScaling (D q.1) ξ f x y).toReal)
        q.2.1 q.2.2.1 q.2.2.2) (P.prod ν) := by
  let : IsProbabilityMeasure P := hgff.isGaussianProcess.isProbabilityMeasure
  apply aemeasurable_pfefferAround_joint_of_ae_pointwise ν
    (D := fun ω x y => (weylScaling (D ω) ξ f x y).toReal)
  · intro x y
    exact hgff.aemeasurable_singular_weyl_point hγ hγ₂ hα hD hf hfc x y
  · exact hgff.ae_singular_weyl_metric hγ hγ₂ hα hD hf

/-- A measurable choice among countably many compactly supported continuous
shifts yields an almost everywhere measurable joint around distance. -/
theorem IsWholePlaneGFF.aemeasurable_singular_countable_weyl_around_joint
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (f : ℕ → ℂ → ℝ) (hf : ∀ n, Continuous (f n))
    (hfc : ∀ n, HasCompactSupport (f n)) {N : Ω → ℕ} (hN : Measurable N)
    (ν : Measure (ℂ × ℝ × ℝ)) [SFinite ν] :
    AEMeasurable (fun q : Ω × (ℂ × ℝ × ℝ) =>
      pfefferAround (fun x y => (weylScaling (D q.1) ξ (f (N q.1)) x y).toReal)
        q.2.1 q.2.2.1 q.2.2.2) (P.prod ν) := by
  apply aemeasurable_nat_select (P := P.prod ν)
    (g := fun n q => pfefferAround
      (fun x y => (weylScaling (D q.1) ξ (f n) x y).toReal)
      q.2.1 q.2.2.1 q.2.2.2) (hN.comp measurable_fst)
  intro n
  exact hgff.aemeasurable_singular_weyl_around_joint hγ hγ₂ hα hD (hf n) (hfc n) ν

end HarmonicBalls
