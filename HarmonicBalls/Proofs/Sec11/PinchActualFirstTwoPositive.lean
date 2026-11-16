import HarmonicBalls.FirstPass.S11an
import HarmonicBalls.FirstPass.S11c.MassPositive
import HarmonicBalls.FirstPass.S11c.ProbAssembly
import HarmonicBalls.FirstPass.S11d.Dyadic
import HarmonicBalls.FirstPass.Phase2.SquarePositiveHolds
import HarmonicBalls.FirstPass.Phase2.DomainMarkovConditionalPositiveHolds
import HarmonicBalls.FirstPass.Phase2.CircleAverageLocalityLinkDerived
import HarmonicBalls.Proofs.Sec11.PinchSecondAnnulusVersionProved
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
open scoped ENNReal

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

/-- A positive-probability exterior event simultaneously bounds the crossing distance
away from zero and the annular Green-potential term from above. -/
theorem IsWholePlaneGFF.exists_positive_outside_pinchLocal_thresholds
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {γ ξ α δ M : ℝ} {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    {U V W T Q' Q : Set ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α hC D)
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ∃ (A : Set Ω) (c₁ c₂ : ℝ),
      MeasurableSet[MeasurableSpace.comap (localModConstPairings α hC (closure W)ᶜ)
        inferInstance] A ∧ 0 < P A ∧ 0 < c₁ ∧ 0 < c₂ ∧
      ∀ᵐ ω ∂P, ω ∈ A → pinchFirstEventLocal (D ω) W T Q' Q δ ∧
        c₁ ≤ setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ)) ∧
        ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6 ≤ ENNReal.ofReal c₂ := by
  obtain ⟨F, hFm, hFp, hFe⟩ := hh.exists_positive_outside_pinchLocal_first hγ hγ₂ hα hD hgeo
  obtain ⟨a, ham, hae, hap⟩ := hh.exists_positive_outside_pinchLocal_crossing hγ hγ₂ hα hD hgeo
  obtain ⟨G, hGm, hGe, hGf⟩ :=
    BundleParts.exists_exterior_annulusGreenPotentialSup_version hgeo hγ hγ₂ hα hh hμ
  let E : ℕ → Set Ω := fun n =>
    {ω | 1 / ((n : ℝ) + 1) ≤ a ω ∧
      ENNReal.ofReal M * G ω ≤ ENNReal.ofReal ((n : ℝ) + 1)}
  have hEm : ∀ n, MeasurableSet[MeasurableSpace.comap
      (localModConstPairings α hC (closure W)ᶜ) inferInstance] (E n) := by
    intro n
    exact (measurableSet_le measurable_const ham).inter
      (measurableSet_le (hGm.const_mul _) measurable_const)
  have hcover : ∀ᵐ ω ∂P, ω ∈ F → ∃ n, ω ∈ E n := by
    filter_upwards [hap, hGf] with ω hωa hωG _
    have hfin : ENNReal.ofReal M * G ω ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωG
    obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hωa
    obtain ⟨n₁, hn₁⟩ := ENNReal.exists_nat_gt hfin
    refine ⟨n₀ + n₁, ?_, ?_⟩
    · have hle : (1 : ℝ) / (((n₀ + n₁ : ℕ) : ℝ) + 1) ≤ 1 / ((n₀ : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        linarith [Nat.cast_nonneg n₁ (α := ℝ)]
      exact hle.trans hn₀.le
    · have h₁ : (n₁ : ℝ≥0∞) = ENNReal.ofReal (n₁ : ℝ) := (ENNReal.ofReal_natCast n₁).symm
      have h₂ : ENNReal.ofReal (n₁ : ℝ) ≤ ENNReal.ofReal (((n₀ + n₁ : ℕ) : ℝ) + 1) :=
        ENNReal.ofReal_le_ofReal (by push_cast; linarith [Nat.cast_nonneg n₀ (α := ℝ)])
      exact hn₁.le.trans (h₁ ▸ h₂)
  have hex : ∃ n, 0 < P (F ∩ E n) := by
    by_contra hcon
    have hU : P (⋃ n : ℕ, F ∩ E n) = 0 :=
      measure_iUnion_null_iff.2 fun n => le_antisymm (not_lt.1 fun h => hcon ⟨n, h⟩) zero_le
    have hsub : F ≤ᵐ[P] ⋃ n : ℕ, F ∩ E n := by
      filter_upwards [hcover] with ω hω hωF
      obtain ⟨n, hn⟩ := hω hωF
      exact mem_iUnion.2 ⟨n, hωF, hn⟩
    have h := measure_mono_ae hsub
    rw [hU] at h
    exact hFp.ne' (le_antisymm h zero_le)
  obtain ⟨n, hn⟩ := hex
  refine ⟨F ∩ E n, 1 / ((n : ℝ) + 1), (n : ℝ) + 1,
    hFm.inter (hEm n), hn, by positivity, by positivity, ?_⟩
  filter_upwards [hFe, hae, hGe] with ω hFω haω hGω hω
  exact ⟨hFω.mp hω.1, haω ▸ hω.2.1, hGω ▸ hω.2.2⟩

/-- A deterministic dyadic square in the inner disk carries arbitrarily large
mass with positive probability. -/
theorem IsWholePlaneGFF.exists_pinch_square_large_mass
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {γ ξ α δ : ℝ} {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    {U V W T Q' Q : Set ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α hC D)
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ∃ S : Set ℂ, IsClosedDyadicSquare S ∧ S ⊆ U ∧
      ∀ C : ℝ, 0 ≤ C → 0 < P {ω | ENNReal.ofReal C < μ ω S} := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨x, hx⟩ := hgeo.U_nonempty
  obtain ⟨S₁, S₂, hS₁, hS₂, hS12, hS₂U⟩ :=
    exists_closedDyadicSquare_pair hgeo.isOpen_U hx
  have hS12' : S₁ ⊆ S₂ := hS12.trans interior_subset
  have hdis : Disjoint S₂ (sphere (0 : ℂ) 1) := by
    refine Set.disjoint_left.mpr fun z hz hs => ?_
    have hz' := hgeo.U_subset (hS₂U hz)
    exact hz'.2 (sphere_subset_closedBall hs)
  have hsup : AEMeasurable (fun ω => ⨆ u ∈ S₂, ⨆ v ∈ S₂,
      internalMetric (D ω) S₂ u v) P := by
    refine lqgMetricSupMeasurableFrozen_derived γ α ξ hγ hγ₂ hα Ω P hC hcirc D hh hD S₂
      ⟨{S₂}, ?_, ?_⟩
    · intro R hR
      rw [Finset.mem_singleton] at hR
      obtain ⟨n, j, k, he⟩ := hS₂
      rw [hR, he]
      exact isClosedRectangle_closedDyadicSquare n j k
    · simp
  have hmass := lqgMeasureSquareMeasurable_derived' γ α hγ hγ₂ hα Ω P hC hcirc μ hh hμ S₁ hS₁
  have hpos := lqgMeasureSquarePositiveFrozen_holds γ α hγ hγ₂ hα Ω P hC hcirc μ hh hμ S₁ hS₁
  refine ⟨S₁, hS₁, hS12'.trans hS₂U, ?_⟩
  intro C hC₀
  have hc : 0 < ENNReal.ofReal (C + 1) := ENNReal.ofReal_pos.2 (by linarith)
  have hp := mass_event_pos_of_shift hγ hγ₂ hα cameronMartinEventTransferFrozen_derived P
    hS₁ hS₂ hS12' hdis hh hμ hD hsup hmass hpos hc ENNReal.ofReal_ne_top
  refine hp.trans_le (measure_mono ?_)
  intro ω hω
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hC₀).2 (by linarith) |>.trans_le hω

/-- The inner disk has conditionally positive probability of carrying any
prescribed finite mass, given the exterior field. -/
theorem IsWholePlaneGFF.pinch_inner_mass_condExp_pos
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {γ ξ α δ : ℝ} {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    {U V W T Q' Q : Set ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α hC D)
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) (C : ℝ) (hC₀ : 0 ≤ C) :
    ∀ᵐ ω ∂P, 0 < (P[({ω | ENNReal.ofReal C < μ ω U}).indicator
      (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap (localModConstPairings α hC (closure W)ᶜ) inferInstance]) ω := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hδ : 0 < 10 * δ := by linarith [hgeo.delta_pos]
  have hUV : closure U ⊆ V := fun x hx => hgeo.buffer_U
    (subset_closure (self_subset_thickening hδ (closure U) hx))
  have hVW : closure V ⊆ W := fun x hx => hgeo.buffer_V
    (subset_closure (self_subset_thickening hδ (closure V) hx))
  obtain ⟨c, rU, rV, rW, hU, _, hW⟩ := hgeo.concentric
  have hUb : Bornology.IsBounded U := by rw [hU]; exact isBounded_ball
  obtain ⟨x, hx⟩ := hgeo.U_nonempty
  have hxW : x ∈ W := hVW (subset_closure (hUV (subset_closure hx)))
  have hrW : 0 < rW := by
    rw [hW] at hxW
    exact dist_nonneg.trans_lt (mem_ball.1 hxW)
  obtain ⟨S, _, hSU, hSpos⟩ := hh.exists_pinch_square_large_mass hγ hγ₂ hα hμ hD hgeo
  have hpos : 0 < P {ω | ENNReal.ofReal C < μ ω U} :=
    (hSpos C hC₀).trans_le (measure_mono fun ω hω => hω.trans_le (measure_mono hSU))
  obtain ⟨g, hgm, hge⟩ := lqgMassInnerMeasurable_derived' γ α Ω P hC hcirc μ hh
    hγ hγ₂ hα hμ V U hgeo.isOpen_V hgeo.isOpen_U hUb hUV
  let A : Set Ω := {ω | ENNReal.ofReal C < g ω}
  have hAm : MeasurableSet[fieldSigmaAlgebra α hC V] A := measurableSet_lt measurable_const hgm
  have hAe : {ω | ENNReal.ofReal C < μ ω U} =ᵐ[P] A := by
    filter_upwards [hge] with ω hω
    simp [A, hω]
  have hAp : 0 < P A := by rw [← measure_congr hAe]; exact hpos
  have hp := domainMarkovConditionalPositive_holds α Ω P hC hcirc hh W V
    ⟨c, rW, hrW, hW⟩ hgeo.isOpen_V hVW A hAm hAp
  have hi : ({ω | ENNReal.ofReal C < μ ω U}).indicator (fun _ => (1 : ℝ)) =ᵐ[P]
      A.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hAe] with ω hω
    have hiff := iff_of_eq hω
    by_cases hmem : ω ∈ {ω | ENNReal.ofReal C < μ ω U}
    · simp [hmem, hiff.mp hmem]
    · have hnot : ω ∉ A := fun h => hmem (hiff.mpr h)
      simp [hmem, hnot]
  filter_upwards [hp, condExp_congr_ae (m := MeasurableSpace.comap
    (localModConstPairings α hC (closure W)ᶜ) inferInstance) hi] with ω hpω he
  rw [he]
  exact hpω

end HarmonicBalls
