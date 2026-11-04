import HarmonicBalls.Proofs.Sec6.FineSupportLaw
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-! # Joint measurability of parameterized pushforwards -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter Topology
open scoped ENNReal

/-- A parameterized measurable pushforward of a measurable family of locally
finite planar measures is measurable. -/
theorem measurable_map_of_locallyFinite
    {A : Type*} [MeasurableSpace A] {μ : A → Measure ℂ}
    (hμ : Measurable μ) (hfinite : ∀ a, IsLocallyFiniteMeasure (μ a))
    {f : A × ℂ → ℂ} (hf : Measurable f) :
    Measurable (fun a => (μ a).map (fun z => f (a, z))) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  let T : Set (A × ℂ) := f ⁻¹' S
  have hT : MeasurableSet T := hf hS
  let κ (n : ℕ) : Kernel A ℂ := ⟨fun a => (μ a).restrict (closedBall 0 n), by
    apply Measure.measurable_of_measurable_coe
    intro U hU
    simp only [Measure.restrict_apply hU]
    exact (Measure.measurable_coe (hU.inter isClosed_closedBall.measurableSet)).comp hμ⟩
  have hκ (n : ℕ) (a : A) : IsFiniteMeasure (κ n a) := by
    have : IsLocallyFiniteMeasure (μ a) := hfinite a
    change IsFiniteMeasure ((μ a).restrict (closedBall 0 n))
    exact ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall (0 : ℂ) (n : ℝ)).measure_lt_top⟩
  have hm (n : ℕ) : Measurable fun a => (κ n a) (Prod.mk a ⁻¹' T) :=
    Kernel.measurable_kernel_prodMk_left_of_finite hT (hκ n)
  have heq (a : A) : (μ a).map (fun z => f (a,z)) S =
      ⨆ n, (κ n a) (Prod.mk a ⁻¹' T) := by
    have hf' : Measurable (fun z => f (a,z)) := hf.comp (measurable_const.prodMk measurable_id)
    rw [Measure.map_apply hf' hS]
    let U : Set ℂ := Prod.mk a ⁻¹' T
    have hUm : MeasurableSet U := hT.preimage (measurable_const.prodMk measurable_id)
    have hmono : Monotone (fun n : ℕ => U ∩ closedBall (0 : ℂ) n) := by
      intro i j hij
      exact inter_subset_inter_right _ (closedBall_subset_closedBall (by exact_mod_cast hij))
    change (μ a) U = _
    rw [← iUnion_inter_closedBall_nat U 0, hmono.measure_iUnion]
    congr 1
    funext n
    exact (Measure.restrict_apply hUm).symm
  simp_rw [heq]
  exact Measurable.iSup hm

/-- An almost-everywhere locally finite measurable family has a measurable,
everywhere locally finite representative. -/
theorem exists_measurable_locallyFinite_rep {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {μ : Ω → Measure ℂ} (hμ : AEMeasurable μ P)
    (hfinite : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω)) :
    ∃ ν : Ω → Measure ℂ, Measurable ν ∧ (∀ ω, IsLocallyFiniteMeasure (ν ω)) ∧ μ =ᵐ[P] ν := by
  classical
  let μ' := hμ.mk μ
  have hm : Measurable μ' := hμ.measurable_mk
  have heq : μ =ᵐ[P] μ' := hμ.ae_eq_mk
  have hf : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ' ω) := by
    filter_upwards [hfinite, heq] with ω hω hωeq
    simpa only [← hωeq] using hω
  obtain ⟨N, hNsub, hNm, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hf)
  let ν : Ω → Measure ℂ := fun ω => if ω ∈ N then 0 else μ' ω
  refine ⟨ν, measurable_const.ite hNm hm, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ N
    · simp only [ν, hω, ↓reduceIte]
      infer_instance
    · have hg : IsLocallyFiniteMeasure (μ' ω) := by
        by_contra hbad
        exact hω (hNsub hbad)
      simpa only [ν, hω, ↓reduceIte] using hg
  · have hnot : ∀ᵐ ω ∂P, ω ∉ N := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_mem_eq] using hNzero
    filter_upwards [heq, hnot] with ω hωeq hω
    simpa only [ν, hω, ↓reduceIte] using hωeq

/-- Joint almost-everywhere measurability of parameterized pushforwards of a
random locally finite measure. -/
theorem aemeasurable_map_prod_of_locallyFinite
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    (hμ : AEMeasurable μ P) (hfinite : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    {f : (Ω × ℂ) × ℂ → ℂ} (hf : Measurable f) :
    AEMeasurable (fun p : Ω × ℂ => (μ p.1).map (fun z => f (p,z)))
      (P.prod volume) := by
  obtain ⟨ν, hν, hνfinite, hνeq⟩ := exists_measurable_locallyFinite_rep hμ hfinite
  have hm := measurable_map_of_locallyFinite (hν.comp measurable_fst)
    (fun p : Ω × ℂ => hνfinite p.1) hf
  apply hm.aemeasurable.congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp hνeq] with p hp
  exact congrArg (fun m : Measure ℂ => m.map (fun z => f (p,z))) hp.symm

/-- Green potentials transform by pullback under a positive affine map. -/
theorem greenPotential_affine {O : Set ℂ} (hO : IsOpen O)
    (hOb : Bornology.IsBounded O) (μ : Measure ℂ) {k : ℝ} (hk : 0 < k)
    (b x : ℂ) :
    greenPotential ((fun z : ℂ => k • z + b) '' O) μ (k • x + b) =
      greenPotential O (μ.map (fun z => k⁻¹ • (z - b))) x := by
  have ho' : IsOpen ((fun z : ℂ => k • z) '' O) :=
    (Homeomorph.smulOfNeZero k hk.ne').isOpenMap _ hO
  have h := greenPotential_translate ho' μ b (k • x)
  rw [greenPotential_dilation hO hOb _ hk] at h
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  simpa only [image_image, Function.comp_def] using h

universe u

/-- Fine-support potential ratios are jointly almost everywhere measurable in
field and centre at each positive scale. -/
theorem aemeasurable_fineSupport_ratio_joint
    (hholder : GreenPotentialHolderStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {r : ℝ} (hr : 0 < r) :
    AEMeasurable (fun p : Ω × ℂ =>
      greenPotentialExtremaRatio (fineSupportAnnulus p.2 r)
        (sphere p.2 (r / 4)) (μ p.1)) (P.prod volume) := by
  let O := fineSupportAnnulus 0 1
  let K := sphere (0 : ℂ) (1 / 4)
  obtain ⟨hO, _, _, hKO, _⟩ := fineSupportAnnulus_geometry 0 (by norm_num : (0 : ℝ) < 1)
  have hopen : IsOpen O := by
    obtain ⟨_, ρ, hρ, heq, _⟩ := hO
    change IsOpen (fineSupportAnnulus 0 1)
    rw [heq]
    exact isOpen_lt hρ.continuous continuous_const
  have hbounded : Bornology.IsBounded O := hO.1
  let m : Ω × ℂ → Measure ℂ := fun p => (μ p.1).map (fun z => r⁻¹ • (z - p.2))
  have hm : AEMeasurable m (P.prod volume) := by
    change AEMeasurable (fun p : Ω × ℂ => (μ p.1).map (fun z => r⁻¹ • (z - p.2))) _
    apply aemeasurable_map_prod_of_locallyFinite (f := fun q : (Ω × ℂ) × ℂ =>
      r⁻¹ • (q.2 - q.1.2)) (h.aemeasurable_lqgMeasure hμ)
    · filter_upwards [hμ] with ω hω
      exact hω.isLocallyFiniteMeasure
    · fun_prop
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hc : ∀ᵐ p ∂(P.prod volume),
      Continuous (fun z : K => greenPotential O (m p) z) ∧
      Continuous (fun z : O => greenPotential O (m p) z) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (hholder γ 0 hγ hγ2 hQ Ω P hC hcirc μ h hμ)] with p hhold
    obtain ⟨ho, _, _, _, _⟩ := fineSupportAnnulus_geometry p.2 hr
    obtain ⟨_, C, δ, hδ, hcont⟩ := hhold (fineSupportAnnulus p.2 r) ho
      (fun _ => 1) (memLp_top_const (1 : ℝ))
    have hcont' : ContinuousOn (greenPotential (fineSupportAnnulus p.2 r) (μ p.1))
        (closure (fineSupportAnnulus p.2 r)) := by
      apply greenPotential_continuousOn_of_holder (μ p.1)
      refine ⟨C, δ, hδ, ?_⟩
      simpa only [mul_one] using hcont
    have hcontinuous (S : Set ℂ) (hS : S ⊆ O) :
        Continuous (fun z : S => greenPotential O (m p) z) := by
      have heq : (fun z : S => greenPotential O (m p) z) =
          (fun z : S => greenPotential (fineSupportAnnulus p.2 r) (μ p.1)
            (r • (z : ℂ) + p.2)) := by
        funext z
        have hcov := greenPotential_affine hopen hbounded (μ p.1) hr p.2 (z : ℂ)
        rw [fineSupportAnnulus_affine p.2 hr] at hcov
        exact hcov.symm
      rw [heq]
      change Continuous (S.domRestrict (fun z : ℂ =>
        greenPotential (fineSupportAnnulus p.2 r) (μ p.1) (r • z + p.2)))
      apply ContinuousOn.domRestrict
      apply hcont'.comp (by fun_prop)
      intro z hz
      apply subset_closure
      rw [← fineSupportAnnulus_affine p.2 hr]
      exact ⟨z, hS hz, rfl⟩
    exact ⟨hcontinuous K hKO, hcontinuous O (Subset.rfl)⟩
  have hratio := aemeasurable_potential_extrema_ratio_of_sections (P.prod volume)
    (fun p (z : K) => greenPotential O (m p) z)
    (fun p (z : O) => greenPotential O (m p) z)
    (fun z => (measurable_greenPotential_measure hopen hbounded z).comp_aemeasurable hm)
    (fun z => (measurable_greenPotential_measure hopen hbounded z).comp_aemeasurable hm) hc
  apply hratio.congr
  filter_upwards [] with p
  have hcov := greenPotentialExtremaRatio_affine hopen hbounded K (μ p.1) hr p.2
  rw [fineSupportAnnulus_affine p.2 hr, fineSupportSphere_affine p.2 hr] at hcov
  exact hcov.symm

/-- Fine-support ratios recur above a positive threshold at almost every centre. -/
theorem ae_ae_fineSupport_ratio_recurs_of_gff_joint
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hnonatom : LQGMeasureNonatomic P γ 0 hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc) :
    ∀ᵐ ω ∂P, ∀ᵐ c ∂(volume : Measure ℂ), ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, ∃ n ≥ N,
      a ≤ greenPotentialExtremaRatio (fineSupportAnnulus c (fineSupportScale n))
        (sphere c (fineSupportScale n / 4)) (μ ω) := by
  apply ae_ae_fineSupport_ratio_recurs_of_gff hholder hfull hgrowth hγ hγ2 h hμ hnonatom hAff hCC
  intro n
  exact aemeasurable_fineSupport_ratio_joint hholder hγ hγ2 h hμ
    (by unfold fineSupportScale; positivity)

end HarmonicBalls.Section6
