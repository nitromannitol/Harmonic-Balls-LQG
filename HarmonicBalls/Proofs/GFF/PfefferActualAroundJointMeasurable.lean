import HarmonicBalls.Proofs.GFF.PfefferSourceMetricCoordinates
import HarmonicBalls.Proofs.GFF.PfefferAroundJointMeasurable
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsDerived
import HarmonicBalls.Steps.Sec11.PinchMetricMeasure
import HarmonicBalls.FirstPass.Phase2.WeylShiftedChainDerived
import HarmonicBalls.FirstPass.Phase2.WeylContinuousShiftDerived
import HarmonicBalls.Steps.Sec11.WeylLocality
import HarmonicBalls.Steps.Sec11.InternalMetricExhaustion
import HarmonicBalls.FirstPass.S11d.SmoothCutoff

/-! # Joint measurability of actual LQG metric observables

Almost everywhere measurable basis infima give a jointly measurable version
of a random Euclidean length metric. This applies to the metric of a shifted
whole-plane Gaussian free field and its unrestricted around observable.
-/

namespace HarmonicBalls

open Set Filter MeasureTheory
open scoped ENNReal Topology

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

/-- A weighted chain infimum remains measurable when its weight is random. -/
theorem aemeasurable_random_weightedChainInf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (D : Ω → ℂ → ℂ → ℝ) (g : Ω → ℂ → ℝ)
    (hg : ∀ z, Measurable fun ω => g ω z)
    (U : Set ℂ) {Q : Set ℂ} (hQ : Q.Countable) (δ : ℝ) (x y : ℂ)
    (hloc : ∀ a b, AEMeasurable (fun ω =>
      LatticeProb.LQG.internalMetric (D ω) (Metric.ball a δ ∩ U) a b) P) :
    AEMeasurable (fun ω => LatticeProb.LQG.weightedChainInf (D ω) (g ω) U Q δ x y) P := by
  have := hQ.to_subtype
  unfold LatticeProb.LQG.weightedChainInf LatticeProb.LQG.weightedChainSum
  refine AEMeasurable.iInf fun m => AEMeasurable.iInf fun w => ?_
  apply Finset.aemeasurable_fun_sum
  intro i hi
  exact (((hg _).exp.ennreal_ofReal).aemeasurable).mul (hloc _ _)

/-- A random continuous Weyl weight with a common oscillation modulus has an
almost everywhere measurable internal metric. -/
theorem aemeasurable_internalMetric_random_weyl
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D E : Ω → ℂ → ℂ → ℝ} {ξ : ℝ} {f : Ω → ℂ → ℝ}
    (hf : ∀ ω, Continuous (f ω)) (hfm : ∀ z, Measurable fun ω => f ω z)
    (hK : ∀ ω, ∃ K, ∀ z, ξ * f ω z ≤ K)
    {δ η : ℕ → ℝ} (hδ : ∀ n, 0 < δ n)
    (hη : ∀ ω n a b, dist a b < δ n → |ξ * f ω a - ξ * f ω b| ≤ η n)
    (hη0 : Tendsto η atTop (𝓝 0)) {U : Set ℂ} (hU : IsOpen U)
    (hloc : ∀ a b r, 0 < r → AEMeasurable (fun ω =>
      LatticeProb.LQG.internalMetric (D ω) (Metric.ball a r ∩ U) a b) P)
    (hD : ∀ᵐ ω ∂P, LatticeProb.LQG.IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, LatticeProb.LQG.IsEuclideanLengthMetric (E ω))
    (hE0 : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ E ω x y)
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      LatticeProb.LQG.weylScaling (D ω) ξ (f ω) x y) (x y : ℂ) :
    AEMeasurable (fun ω => LatticeProb.LQG.internalMetric (E ω) U x y) P := by
  by_cases hx : x ∈ U
  swap
  · simp_rw [LatticeProb.LQG.internalMetric_eq_top_of_not_mem _ hx y]
    exact aemeasurable_const
  obtain ⟨Q, hQc, hQd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have hm : AEMeasurable (fun ω => ⨅ n, ENNReal.ofReal (Real.exp (η n)) *
      LatticeProb.LQG.weightedChainInf (D ω) (fun z => ξ * f ω z) U Q (δ n) x y) P :=
    AEMeasurable.iInf fun n => (aemeasurable_random_weightedChainInf D
      (fun ω z => ξ * f ω z) (fun z => (hfm z).const_mul ξ) U hQc (δ n) x y
      (fun a b => hloc a b (δ n) (hδ n))).const_mul _
  refine hm.congr ?_
  filter_upwards [hD, hE, hE0, hscale] with ω hDω hEω hE0ω hsω
  obtain ⟨K, hKω⟩ := hK ω
  exact (LatticeProb.LQG.internalMetric_weylScaling_eq_iInf_weightedChainInf
    hDω hEω hE0ω (hf ω) hKω hsω hU hQd hδ (hη ω) hη0 hx y).symm

/-- Random compactly supported shifts with a common oscillation modulus have
almost everywhere measurable Weyl-scaled point distances. -/
theorem IsWholePlaneGFF.aemeasurable_singular_random_weyl_point_of_modulus
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) {f : Ω → ℂ → ℝ}
    (hf : ∀ ω, Continuous (f ω)) (hfc : ∀ ω, HasCompactSupport (f ω))
    (hfm : ∀ z, Measurable fun ω => f ω z)
    {δ η : ℕ → ℝ} (hδ : ∀ n, 0 < δ n)
    (hη : ∀ ω n a b, dist a b < δ n → |ξ * f ω a - ξ * f ω b| ≤ η n)
    (hη0 : Tendsto η atTop (𝓝 0)) (x y : ℂ) :
    AEMeasurable (fun ω => (weylScaling (D ω) ξ (f ω) x y).toReal) P := by
  have haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc :=
    lqgMetricFieldAxiomsUnivFrozen_derived Ω P γ ξ α₀ hC hcirc
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms
    P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD
  have hshift : ∀ᵐ ω ∂P, IsEuclideanLengthMetric
      (fun a b => (weylScaling (D ω) ξ (f ω) a b).toReal) := by
    filter_upwards [hmetric] with ω hm
    exact (hm.weylScaling_continuous_isEuclideanLengthMetric ξ (hf ω)).2
  have hopen := aemeasurable_internalMetric_random_weyl
    (D := D) (E := fun ω a b => (weylScaling (D ω) ξ (f ω) a b).toReal)
    hf hfm (fun ω => exists_const_mul_le_of_hasCompactSupport (hf ω) (hfc ω) ξ)
    hδ hη hη0 isOpen_univ
    (fun a b r _ => aemeasurable_internalMetric_of_fieldAxioms
      lqgMetricFieldAxiomsUnivFrozen_derived hγ hγ₂ hα hgff hD
      (Metric.isOpen_ball.inter isOpen_univ) a b)
    (by filter_upwards [hmetric] with ω hm; exact (LPBridge.isEuclideanLengthMetric_iff _).1 hm)
    (by filter_upwards [hshift] with ω hm; exact (LPBridge.isEuclideanLengthMetric_iff _).1 hm)
    (Eventually.of_forall fun _ _ _ => ENNReal.toReal_nonneg)
    (by
      filter_upwards [hmetric] with ω hm
      intro a b
      exact ENNReal.ofReal_toReal ((hm.weylScaling_continuous_isEuclideanLengthMetric ξ (hf ω)).1 a b).ne)
    x y
  have hp : AEMeasurable (fun ω => ENNReal.ofReal
      ((weylScaling (D ω) ξ (f ω) x y).toReal)) P := by
    apply hopen.congr
    filter_upwards [hshift] with ω hm
    exact (hm.ofReal_eq_internalMetric x y).symm
  simpa using hp.ennreal_toReal

/-- The around distance of random compactly supported Weyl shifts with a
common oscillation modulus is jointly almost everywhere measurable. -/
theorem IsWholePlaneGFF.aemeasurable_singular_random_weyl_around_joint_of_modulus
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) {f : Ω → ℂ → ℝ}
    (hf : ∀ ω, Continuous (f ω)) (hfc : ∀ ω, HasCompactSupport (f ω))
    (hfm : ∀ z, Measurable fun ω => f ω z)
    {δ η : ℕ → ℝ} (hδ : ∀ n, 0 < δ n)
    (hη : ∀ ω n a b, dist a b < δ n → |ξ * f ω a - ξ * f ω b| ≤ η n)
    (hη0 : Tendsto η atTop (𝓝 0)) (ν : Measure (ℂ × ℝ × ℝ)) [SFinite ν] :
    AEMeasurable (fun q : Ω × (ℂ × ℝ × ℝ) =>
      pfefferAround (fun x y => (weylScaling (D q.1) ξ (f q.1) x y).toReal)
        q.2.1 q.2.2.1 q.2.2.2) (P.prod ν) := by
  let : IsProbabilityMeasure P := hgff.isGaussianProcess.isProbabilityMeasure
  apply aemeasurable_pfefferAround_joint_of_ae_pointwise ν
    (D := fun ω x y => (weylScaling (D ω) ξ (f ω) x y).toReal)
  · intro x y
    exact hgff.aemeasurable_singular_random_weyl_point_of_modulus hγ hγ₂ hα hD hf hfc hfm
      hδ hη hη0 x y
  · have haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc :=
      lqgMetricFieldAxiomsUnivFrozen_derived Ω P γ ξ α₀ hC hcirc
    have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms
      P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD
    filter_upwards [hmetric] with ω hm
    exact (hm.weylScaling_continuous_isEuclideanLengthMetric ξ (hf ω)).2

/-- Measurably selected oscillation scales give a measurable random Weyl
internal metric. -/
theorem aemeasurable_internalMetric_random_weyl_of_selected_scales
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D E : Ω → ℂ → ℂ → ℝ} {ξ : ℝ} {f : Ω → ℂ → ℝ}
    (hf : ∀ ω, Continuous (f ω)) (hfm : ∀ z, Measurable fun ω => f ω z)
    (hK : ∀ ω, ∃ K, ∀ z, ξ * f ω z ≤ K)
    {δ η : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) {N : ℕ → Ω → ℕ}
    (hN : ∀ n, Measurable (N n))
    (hη : ∀ ω n a b, dist a b < δ (N n ω) → |ξ * f ω a - ξ * f ω b| ≤ η n)
    (hη0 : Tendsto η atTop (𝓝 0)) {U : Set ℂ} (hU : IsOpen U)
    (hloc : ∀ a b r, 0 < r → AEMeasurable (fun ω =>
      LatticeProb.LQG.internalMetric (D ω) (Metric.ball a r ∩ U) a b) P)
    (hD : ∀ᵐ ω ∂P, LatticeProb.LQG.IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, LatticeProb.LQG.IsEuclideanLengthMetric (E ω))
    (hE0 : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ E ω x y)
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      LatticeProb.LQG.weylScaling (D ω) ξ (f ω) x y) (x y : ℂ) :
    AEMeasurable (fun ω => LatticeProb.LQG.internalMetric (E ω) U x y) P := by
  by_cases hx : x ∈ U
  swap
  · simp_rw [LatticeProb.LQG.internalMetric_eq_top_of_not_mem _ hx y]
    exact aemeasurable_const
  obtain ⟨Q, hQc, hQd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have hm : AEMeasurable (fun ω => ⨅ n, ENNReal.ofReal (Real.exp (η n)) *
      LatticeProb.LQG.weightedChainInf (D ω) (fun z => ξ * f ω z) U Q (δ (N n ω)) x y) P := by
    refine AEMeasurable.iInf fun n => (aemeasurable_nat_select (g := fun m ω =>
      LatticeProb.LQG.weightedChainInf (D ω) (fun z => ξ * f ω z) U Q (δ m) x y)
      (hN n) ?_).const_mul _
    intro m
    exact aemeasurable_random_weightedChainInf D
      (fun ω z => ξ * f ω z) (fun z => (hfm z).const_mul ξ) U hQc (δ m) x y
      (fun a b => hloc a b (δ m) (hδ m))
  refine hm.congr ?_
  filter_upwards [hD, hE, hE0, hscale] with ω hDω hEω hE0ω hsω
  obtain ⟨K, hKω⟩ := hK ω
  exact (LatticeProb.LQG.internalMetric_weylScaling_eq_iInf_weightedChainInf
    hDω hEω hE0ω (hf ω) hKω hsω hU hQd (fun n => hδ (N n ω)) (hη ω) hη0 hx y).symm

/-- Random compactly supported shifts with measurable oscillation scales have
almost everywhere measurable Weyl-scaled point distances. -/
theorem IsWholePlaneGFF.aemeasurable_singular_random_weyl_point_of_selected_scales
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) {f : Ω → ℂ → ℝ}
    (hf : ∀ ω, Continuous (f ω)) (hfc : ∀ ω, HasCompactSupport (f ω))
    (hfm : ∀ z, Measurable fun ω => f ω z)
    {δ η : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) {N : ℕ → Ω → ℕ}
    (hN : ∀ n, Measurable (N n))
    (hη : ∀ ω n a b, dist a b < δ (N n ω) → |ξ * f ω a - ξ * f ω b| ≤ η n)
    (hη0 : Tendsto η atTop (𝓝 0)) (x y : ℂ) :
    AEMeasurable (fun ω => (weylScaling (D ω) ξ (f ω) x y).toReal) P := by
  have haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc :=
    lqgMetricFieldAxiomsUnivFrozen_derived Ω P γ ξ α₀ hC hcirc
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms
    P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD
  have hshift : ∀ᵐ ω ∂P, IsEuclideanLengthMetric
      (fun a b => (weylScaling (D ω) ξ (f ω) a b).toReal) := by
    filter_upwards [hmetric] with ω hm
    exact (hm.weylScaling_continuous_isEuclideanLengthMetric ξ (hf ω)).2
  have hopen := aemeasurable_internalMetric_random_weyl_of_selected_scales
    (D := D) (E := fun ω a b => (weylScaling (D ω) ξ (f ω) a b).toReal)
    hf hfm (fun ω => exists_const_mul_le_of_hasCompactSupport (hf ω) (hfc ω) ξ)
    hδ hN hη hη0 isOpen_univ
    (fun a b r _ => aemeasurable_internalMetric_of_fieldAxioms
      lqgMetricFieldAxiomsUnivFrozen_derived hγ hγ₂ hα hgff hD
      (Metric.isOpen_ball.inter isOpen_univ) a b)
    (by filter_upwards [hmetric] with ω hm; exact (LPBridge.isEuclideanLengthMetric_iff _).1 hm)
    (by filter_upwards [hshift] with ω hm; exact (LPBridge.isEuclideanLengthMetric_iff _).1 hm)
    (Eventually.of_forall fun _ _ _ => ENNReal.toReal_nonneg)
    (by
      filter_upwards [hmetric] with ω hm
      intro a b
      exact ENNReal.ofReal_toReal ((hm.weylScaling_continuous_isEuclideanLengthMetric ξ (hf ω)).1 a b).ne)
    x y
  have hp : AEMeasurable (fun ω => ENNReal.ofReal
      ((weylScaling (D ω) ξ (f ω) x y).toReal)) P := by
    apply hopen.congr
    filter_upwards [hshift] with ω hm
    exact (hm.ofReal_eq_internalMetric x y).symm
  simpa using hp.ennreal_toReal

/-- The around distance of random compactly supported Weyl shifts with
measurable oscillation scales is jointly almost everywhere measurable. -/
theorem IsWholePlaneGFF.aemeasurable_singular_random_weyl_around_joint_of_selected_scales
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) {f : Ω → ℂ → ℝ}
    (hf : ∀ ω, Continuous (f ω)) (hfc : ∀ ω, HasCompactSupport (f ω))
    (hfm : ∀ z, Measurable fun ω => f ω z)
    {δ η : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) {N : ℕ → Ω → ℕ}
    (hN : ∀ n, Measurable (N n))
    (hη : ∀ ω n a b, dist a b < δ (N n ω) → |ξ * f ω a - ξ * f ω b| ≤ η n)
    (hη0 : Tendsto η atTop (𝓝 0)) (ν : Measure (ℂ × ℝ × ℝ)) [SFinite ν] :
    AEMeasurable (fun q : Ω × (ℂ × ℝ × ℝ) =>
      pfefferAround (fun x y => (weylScaling (D q.1) ξ (f q.1) x y).toReal)
        q.2.1 q.2.2.1 q.2.2.2) (P.prod ν) := by
  let : IsProbabilityMeasure P := hgff.isGaussianProcess.isProbabilityMeasure
  apply aemeasurable_pfefferAround_joint_of_ae_pointwise ν
    (D := fun ω x y => (weylScaling (D ω) ξ (f ω) x y).toReal)
  · intro x y
    exact hgff.aemeasurable_singular_random_weyl_point_of_selected_scales hγ hγ₂ hα hD hf hfc hfm
      hδ hN hη hη0 x y
  · have haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc :=
      lqgMetricFieldAxiomsUnivFrozen_derived Ω P γ ξ α₀ hC hcirc
    have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms
      P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD
    filter_upwards [hmetric] with ω hm
    exact (hm.weylScaling_continuous_isEuclideanLengthMetric ξ (hf ω)).2

/-- Uniformly continuous random functions admit measurable oscillation scales. -/
theorem measurable_oscillation_scales
    {Ω : Type*} [MeasurableSpace Ω] {g : Ω → ℂ → ℝ}
    (hc : ∀ ω, Continuous (g ω)) (hm : ∀ z, Measurable fun ω => g ω z)
    (hu : ∀ ω, UniformContinuous (g ω)) :
    ∃ N : ℕ → Ω → ℕ, (∀ n, Measurable (N n)) ∧
      ∀ ω n a b, dist a b < 1 / ((N n ω : ℝ) + 1) →
        |g ω a - g ω b| ≤ 1 / ((n : ℝ) + 1) := by
  classical
  obtain ⟨Q, hQc, hQd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have := hQc.to_subtype
  let good : ℕ → ℕ → Ω → Prop := fun n m ω => ∀ a b : Q,
    dist (a : ℂ) b < 1 / ((m : ℝ) + 1) →
      |g ω a - g ω b| ≤ 1 / ((n : ℝ) + 1)
  have hgood : ∀ n m, MeasurableSet {ω | good n m ω} := by
    intro n m
    simp only [good, Set.ofPred_forall]
    exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      MeasurableSet.iInter fun _ => measurableSet_le (((hm a).sub (hm b)).abs) measurable_const
  have hex : ∀ n ω, ∃ m, good n m ω := by
    intro n ω
    obtain ⟨ε, hε, hεg⟩ := Metric.uniformContinuous_iff.mp (hu ω)
      (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    refine ⟨m, ?_⟩
    intro a b hab
    have h := hεg (lt_trans hab hm)
    rw [Real.dist_eq] at h
    exact h.le
  let N : ℕ → Ω → ℕ := fun n ω => Nat.find (hex n ω)
  refine ⟨N, fun n => measurable_find (hex n) (hgood n), ?_⟩
  intro ω n a b hab
  have hclosed : IsClosed {p : ℂ × ℂ |
      1 / ((N n ω : ℝ) + 1) ≤ dist p.1 p.2 ∨
        |g ω p.1 - g ω p.2| ≤ 1 / ((n : ℝ) + 1)} := by
    exact (isClosed_le continuous_const (continuous_fst.dist continuous_snd)).union
      (isClosed_le (((hc ω).comp continuous_fst).sub ((hc ω).comp continuous_snd)).abs continuous_const)
  have hall := (hQd.prod hQd).induction (P := fun p : ℂ × ℂ =>
      1 / ((N n ω : ℝ) + 1) ≤ dist p.1 p.2 ∨
        |g ω p.1 - g ω p.2| ≤ 1 / ((n : ℝ) + 1)) ?_ hclosed (a, b)
  · exact hall.resolve_left (not_le_of_gt hab)
  · intro p hp
    by_cases hd : dist p.1 p.2 < 1 / ((N n ω : ℝ) + 1)
    · exact Or.inr (Nat.find_spec (hex n ω) ⟨p.1, hp.1⟩ ⟨p.2, hp.2⟩ hd)
    · exact Or.inl (le_of_not_gt hd)

/-- A pointwise measurable random continuous compactly supported shift has
almost everywhere measurable Weyl-scaled point distances. -/
theorem IsWholePlaneGFF.aemeasurable_singular_random_weyl_point
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) {f : Ω → ℂ → ℝ}
    (hf : ∀ ω, Continuous (f ω)) (hfc : ∀ ω, HasCompactSupport (f ω))
    (hfm : ∀ z, Measurable fun ω => f ω z) (x y : ℂ) :
    AEMeasurable (fun ω => (weylScaling (D ω) ξ (f ω) x y).toReal) P := by
  obtain ⟨N, hN, hη⟩ := measurable_oscillation_scales
    (g := fun ω z => ξ * f ω z)
    (fun ω => continuous_const.mul (hf ω))
    (fun z => (hfm z).const_mul ξ)
    (fun ω => uniformContinuous_const_mul_of_hasCompactSupport (hf ω) (hfc ω) ξ)
  exact hgff.aemeasurable_singular_random_weyl_point_of_selected_scales
    (δ := fun n => 1 / ((n : ℝ) + 1)) (η := fun n => 1 / ((n : ℝ) + 1))
    hγ hγ₂ hα hD hf hfc hfm (fun n => Nat.one_div_pos_of_nat) hN hη
    tendsto_one_div_add_atTop_nhds_zero_nat x y

/-- The around distance of a pointwise measurable random continuous
compactly supported Weyl shift is jointly almost everywhere measurable. -/
theorem IsWholePlaneGFF.aemeasurable_singular_random_weyl_around_joint
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) {f : Ω → ℂ → ℝ}
    (hf : ∀ ω, Continuous (f ω)) (hfc : ∀ ω, HasCompactSupport (f ω))
    (hfm : ∀ z, Measurable fun ω => f ω z)
    (ν : Measure (ℂ × ℝ × ℝ)) [SFinite ν] :
    AEMeasurable (fun q : Ω × (ℂ × ℝ × ℝ) =>
      pfefferAround (fun x y => (weylScaling (D q.1) ξ (f q.1) x y).toReal)
        q.2.1 q.2.2.1 q.2.2.2) (P.prod ν) := by
  let : IsProbabilityMeasure P := hgff.isGaussianProcess.isProbabilityMeasure
  apply aemeasurable_pfefferAround_joint_of_ae_pointwise ν
    (D := fun ω x y => (weylScaling (D ω) ξ (f ω) x y).toReal)
  · intro x y
    exact hgff.aemeasurable_singular_random_weyl_point hγ hγ₂ hα hD hf hfc hfm x y
  · have haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc :=
      lqgMetricFieldAxiomsUnivFrozen_derived Ω P γ ξ α₀ hC hcirc
    have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms
      P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD
    filter_upwards [hmetric] with ω hm
    exact (hm.weylScaling_continuous_isEuclideanLengthMetric ξ (hf ω)).2

/-- A pointwise measurable random continuous shift has almost everywhere
measurable Weyl-scaled point distances. -/
theorem IsWholePlaneGFF.aemeasurable_singular_random_continuous_weyl_point
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) {f : Ω → ℂ → ℝ}
    (hf : ∀ ω, Continuous (f ω)) (hfm : ∀ z, Measurable fun ω => f ω z) (x y : ℂ) :
    AEMeasurable (fun ω => (weylScaling (D ω) ξ (f ω) x y).toReal) P := by
  have hcut : ∀ n : ℕ, ∃ χ : ℂ → ℝ, Continuous χ ∧ HasCompactSupport χ ∧
      ∀ z ∈ Metric.ball (0 : ℂ) n, χ z = 1 := by
    intro n
    obtain ⟨χ, hc, hcs, _, _, he⟩ := exists_smooth_cutoff
      (K := Metric.closedBall (0 : ℂ) n) (U := Metric.ball 0 ((n : ℝ) + 1))
      (isCompact_closedBall _ _) Metric.isOpen_ball
      (Metric.closedBall_subset_ball (by linarith)) Metric.isBounded_ball
    exact ⟨χ, hc.continuous, hcs, fun z hz => he z (Metric.ball_subset_closedBall hz)⟩
  choose χ hχc hχs hχ1 using hcut
  let F : ℕ → Ω → ℂ → ℝ := fun n ω z => χ n z * f ω z
  have hFc : ∀ n ω, Continuous (F n ω) := fun n ω => (hχc n).mul (hf ω)
  have hFs : ∀ n ω, HasCompactSupport (F n ω) := fun n ω => (hχs n).mul_right
  have hFm : ∀ n z, Measurable fun ω => F n ω z := fun n z => (hfm z).const_mul (χ n z)
  have haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc :=
    lqgMetricFieldAxiomsUnivFrozen_derived Ω P γ ξ α₀ hC hcirc
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms
    P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD
  have hinner : ∀ n, AEMeasurable (fun ω => internalMetric
      (fun a b => (weylScaling (D ω) ξ (F n ω) a b).toReal)
      (Metric.ball 0 n) x y) P := by
    intro n
    obtain ⟨N, hN, hη⟩ := measurable_oscillation_scales
      (g := fun ω z => ξ * F n ω z)
      (fun ω => continuous_const.mul (hFc n ω))
      (fun z => (hFm n z).const_mul ξ)
      (fun ω => uniformContinuous_const_mul_of_hasCompactSupport (hFc n ω) (hFs n ω) ξ)
    have hshift : ∀ᵐ ω ∂P, IsEuclideanLengthMetric
        (fun a b => (weylScaling (D ω) ξ (F n ω) a b).toReal) := by
      filter_upwards [hmetric] with ω hm
      exact (hm.weylScaling_continuous_isEuclideanLengthMetric ξ (hFc n ω)).2
    exact aemeasurable_internalMetric_random_weyl_of_selected_scales
      (D := D) (E := fun ω a b => (weylScaling (D ω) ξ (F n ω) a b).toReal)
      (δ := fun n => 1 / ((n : ℝ) + 1)) (η := fun n => 1 / ((n : ℝ) + 1))
      (hFc n) (hFm n) (fun ω => exists_const_mul_le_of_hasCompactSupport (hFc n ω) (hFs n ω) ξ)
      (fun n => Nat.one_div_pos_of_nat) hN hη tendsto_one_div_add_atTop_nhds_zero_nat
      Metric.isOpen_ball
      (fun a b r _ => aemeasurable_internalMetric_of_fieldAxioms
        lqgMetricFieldAxiomsUnivFrozen_derived hγ hγ₂ hα hgff hD
        (Metric.isOpen_ball.inter Metric.isOpen_ball) a b)
      (by filter_upwards [hmetric] with ω hm; exact (LPBridge.isEuclideanLengthMetric_iff _).1 hm)
      (by filter_upwards [hshift] with ω hm; exact (LPBridge.isEuclideanLengthMetric_iff _).1 hm)
      (Eventually.of_forall fun _ _ _ => ENNReal.toReal_nonneg)
      (by
        filter_upwards [hmetric] with ω hm
        intro a b
        exact ENNReal.ofReal_toReal ((hm.weylScaling_continuous_isEuclideanLengthMetric ξ (hFc n ω)).1 a b).ne)
      x y
  have hmeas : AEMeasurable (fun ω => ⨅ n, internalMetric
      (fun a b => (weylScaling (D ω) ξ (F n ω) a b).toReal)
      (Metric.ball 0 n) x y) P := AEMeasurable.iInf hinner
  have hp : AEMeasurable (fun ω => ENNReal.ofReal
      ((weylScaling (D ω) ξ (f ω) x y).toReal)) P := by
    apply hmeas.congr
    filter_upwards [hmetric] with ω hm
    let E := fun a b => (weylScaling (D ω) ξ (f ω) a b).toReal
    have hE := hm.weylScaling_continuous_isEuclideanLengthMetric ξ (hf ω)
    have hlocal : ∀ n : ℕ, internalMetric E (Metric.ball 0 n) x y = internalMetric
        (fun a b => (weylScaling (D ω) ξ (F n ω) a b).toReal)
        (Metric.ball 0 n) x y := by
      intro n
      have hFn := hm.weylScaling_continuous_isEuclideanLengthMetric ξ (hFc n ω)
      apply hm.internalMetric_weylScaling_eq_of_eqOn hE.2 hFn.2 ξ (f ω) (F n ω)
        (fun a b => ENNReal.ofReal_toReal (hE.1 a b).ne)
        (fun a b => ENNReal.ofReal_toReal (hFn.1 a b).ne) Metric.isOpen_ball
      intro z hz
      simp [F, hχ1 n z hz]
    have hunion : (⋃ n : ℕ, Metric.ball (0 : ℂ) n) = univ := Metric.iUnion_ball_nat _
    have hmono : Monotone (fun n : ℕ => Metric.ball (0 : ℂ) n) :=
      fun i j hij => Metric.ball_subset_ball (by exact_mod_cast hij)
    have h := internalMetric_iUnion_of_monotone_isOpen E
      (fun n => Metric.ball 0 n) (fun _ => Metric.isOpen_ball) hmono x y
    rw [hunion, ← hE.2.ofReal_eq_internalMetric x y] at h
    exact (h.trans (iInf_congr hlocal)).symm
  simpa using hp.ennreal_toReal

/-- The around distance of a pointwise measurable random continuous Weyl
shift is jointly almost everywhere measurable. -/
theorem IsWholePlaneGFF.aemeasurable_singular_random_continuous_weyl_around_joint
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) {f : Ω → ℂ → ℝ}
    (hf : ∀ ω, Continuous (f ω)) (hfm : ∀ z, Measurable fun ω => f ω z)
    (ν : Measure (ℂ × ℝ × ℝ)) [SFinite ν] :
    AEMeasurable (fun q : Ω × (ℂ × ℝ × ℝ) =>
      pfefferAround (fun x y => (weylScaling (D q.1) ξ (f q.1) x y).toReal)
        q.2.1 q.2.2.1 q.2.2.2) (P.prod ν) := by
  let : IsProbabilityMeasure P := hgff.isGaussianProcess.isProbabilityMeasure
  apply aemeasurable_pfefferAround_joint_of_ae_pointwise ν
    (D := fun ω x y => (weylScaling (D ω) ξ (f ω) x y).toReal)
  · intro x y
    exact hgff.aemeasurable_singular_random_continuous_weyl_point hγ hγ₂ hα hD hf hfm x y
  · have haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc :=
      lqgMetricFieldAxiomsUnivFrozen_derived Ω P γ ξ α₀ hC hcirc
    have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms
      P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD
    filter_upwards [hmetric] with ω hm
    exact (hm.weylScaling_continuous_isEuclideanLengthMetric ξ (hf ω)).2

/-- A continuous random Weyl shift of a singular metric has a measurable
continuous metric representative, equal at all pairs on one field event. -/
theorem IsWholePlaneGFF.exists_measurable_singular_random_continuous_weyl_metric
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) {f : Ω → ℂ → ℝ}
    (hf : ∀ ω, Continuous (f ω)) (hfm : ∀ z, Measurable fun ω => f ω z) :
    ∃ G : Ω → C(ℂ × ℂ, ℝ), Measurable G ∧
      (∀ ω, IsEuclideanLengthMetric fun x y => G ω (x, y)) ∧
      ∀ᵐ ω ∂P, ∀ x y, G ω (x, y) = (weylScaling (D ω) ξ (f ω) x y).toReal := by
  apply exists_measurable_continuousMap_of_ae_pointwise
  · intro x y
    exact hgff.aemeasurable_singular_random_continuous_weyl_point hγ hγ₂ hα hD hf hfm x y
  · have haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc :=
      lqgMetricFieldAxiomsUnivFrozen_derived Ω P γ ξ α₀ hC hcirc
    have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms
      P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD
    filter_upwards [hmetric] with ω hm
    exact (hm.weylScaling_continuous_isEuclideanLengthMetric ξ (hf ω)).2

end HarmonicBalls
