import HarmonicBalls.Proofs.Sec5.LQGIntegralLaw
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! # Open-set masses from compactly supported test functions -/

namespace HarmonicBalls

universe u

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal Pointwise

/-- Each open subset of the plane has a countable family of nonnegative
compactly supported cutoffs whose integrals recover its mass for every locally
finite measure. -/
theorem exists_open_mass_test_functions {U : Set ℂ} (hU : IsOpen U) :
    ∃ f : ℕ → ℂ → ℝ,
      (∀ n, Continuous (f n)) ∧ (∀ n, HasCompactSupport (f n)) ∧
      ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ →
        μ U = ⨆ n, ENNReal.ofReal (∫ z, f n z ∂μ) := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K : CompactExhaustion U := CompactExhaustion.choice U
  let C : ℕ → Set ℂ := fun n => Subtype.val '' K n
  have hC (n : ℕ) : IsCompact (C n) := (K.isCompact n).image continuous_subtype_val
  have hCU (n : ℕ) : C n ⊆ U := by
    rintro z ⟨x, hx, rfl⟩
    exact x.property
  have hmono : Monotone C := fun i j hij => image_mono (K.subset hij)
  have hcover : (⋃ n, C n) = U := by
    rw [← image_iUnion, K.iUnion_eq, image_univ]
    exact Subtype.range_coe
  have hcut (n : ℕ) : ∃ g : C(ℂ, ℝ), EqOn g 1 (C n) ∧ EqOn g 0 Uᶜ ∧
      HasCompactSupport g ∧ ∀ z, g z ∈ Icc (0 : ℝ) 1 :=
    exists_continuous_one_zero_of_isCompact (hC n) hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (hCU n))
  choose g hgOne hgZero hgComp hgRange using hcut
  refine ⟨fun n => g n, fun n => (g n).continuous, hgComp, ?_⟩
  intro μ hμ
  let _ := hμ
  apply le_antisymm
  · rw [← hcover, hmono.measure_iUnion]
    apply iSup_le
    intro n
    apply le_iSup_of_le n
    apply ((g n).continuous.integrable_of_hasCompactSupport (hgComp n)).measure_le_integral
    · exact Filter.Eventually.of_forall fun z => (hgRange n z).1
    · intro z hz
      simpa using le_of_eq (hgOne n hz).symm
  · apply iSup_le
    intro n
    apply integral_le_measure
    · intro z hz
      exact (hgRange n z).2
    · intro z hz
      exact le_of_eq (hgZero n hz)

/-- The original and normalized LQG measures have the same joint law on any
countable family of open sets. -/
theorem IsWholePlaneGFF.identDistrib_normalizedPullback_open_masses
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {k : ℝ} (hk : 0 < k) (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i)) :
    IdentDistrib (fun ω i => μ ω (U i))
      (fun ω i => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω) (U i)) P P := by
  classical
  choose f hf hfc hmass using fun i => exists_open_mass_test_functions (hU i)
  let F : (ι × ℕ → ℝ) → ι → ℝ≥0∞ := fun x i => ⨆ n, ENNReal.ofReal (x (i, n))
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro i
    exact Measurable.iSup fun n => (measurable_pi_apply (i, n)).ennreal_ofReal
  have hd := (h.identDistrib_normalizedPullback_integrals hAff hCC hγ hγ2 hα hμ hk
    (f := fun p : ι × ℕ => f p.1 p.2) (fun p => hf p.1 p.2)
    (fun p => hfc p.1 p.2)).comp hF
  have hscaled := isLQGMeasureOfField_normalizedPullback hCC h hγ hγ2 hα hμ hk
  have heq₁ : (F ∘ fun ω p => ∫ z, f p.1 p.2 z ∂(μ ω)) =ᵐ[P]
      (fun ω i => μ ω (U i)) := by
    filter_upwards [hμ] with ω hω
    funext i
    exact (hmass i (μ ω) hω.isLocallyFiniteMeasure).symm
  have heq₂ : (F ∘ fun ω p => ∫ z, f p.1 p.2 z ∂
      (normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω))) =ᵐ[P]
      (fun ω i => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω) (U i)) := by
    filter_upwards [hscaled] with ω hω
    funext i
    exact (hmass i _ hω.isLocallyFiniteMeasure).symm
  exact ((IdentDistrib.of_ae_eq hd.aemeasurable_fst heq₁).symm.trans hd).trans
    (IdentDistrib.of_ae_eq hd.aemeasurable_snd heq₂)

/-- A locally finite random measure is measurable if its masses on open sets
are measurable. -/
theorem measurable_measure_of_isOpen {Ω : Type*} [MeasurableSpace Ω]
    {ν : Ω → Measure ℂ} (hloc : ∀ ω, IsLocallyFiniteMeasure (ν ω))
    (hopen : ∀ U : Set ℂ, IsOpen U → Measurable (fun ω => ν ω U)) : Measurable ν := by
  let B : ℕ → Set ℂ := fun n => Metric.ball 0 n
  have hB (n : ℕ) : IsOpen (B n) := Metric.isOpen_ball
  have hfinite (n : ℕ) (ω : Ω) : IsFiniteMeasure ((ν ω).restrict (B n)) := by
    let _ := hloc ω
    apply isFiniteMeasure_restrict.mpr
    apply ne_of_lt
    exact lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      ((isCompact_closedBall 0 n).measure_lt_top)
  have hres (n : ℕ) : Measurable (fun ω => (ν ω).restrict (B n)) := by
    let _ : ∀ ω, IsFiniteMeasure ((ν ω).restrict (B n)) := hfinite n
    apply Measurable.measure_of_isPiSystem BorelSpace.measurable_eq isPiSystem_isOpen
    · intro U hU
      change IsOpen U at hU
      simpa only [Measure.restrict_apply hU.measurableSet] using hopen (U ∩ B n) (hU.inter (hB n))
    · simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter] using hopen (B n) (hB n)
  apply Measure.measurable_measure.mpr
  intro S hS
  have heq (ω : Ω) : ν ω S = ⨆ n, ((ν ω).restrict (B n)) S := by
    simp only [Measure.restrict_apply hS]
    rw [← Monotone.measure_iUnion]
    · change ν ω S = ν ω (⋃ n : ℕ, S ∩ Metric.ball 0 n)
      rw [← inter_iUnion, Metric.iUnion_ball_nat, inter_univ]
    · intro i j hij
      exact inter_subset_inter_right S (Metric.ball_subset_ball (by exact_mod_cast hij))
  simp_rw [heq]
  exact Measurable.iSup fun n => (Measure.measurable_coe hS).comp (hres n)

/-- An LQG measure is almost-everywhere measurable as a measure-valued map. -/
theorem IsWholePlaneGFF.aemeasurable_lqgMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    AEMeasurable μ P := by
  classical
  let η : ℕ → Ω → Measure ℂ := fun n =>
    (h.aemeasurable_lqgApprox γ α₀ n).mk _
  have hη (n : ℕ) : Measurable (η n) := (h.aemeasurable_lqgApprox γ α₀ n).measurable_mk
  have hηeq : ∀ᵐ ω ∂P, ∀ n, η n ω =
      lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale n) := by
    apply ae_all_iff.mpr
    intro n
    exact (h.aemeasurable_lqgApprox γ α₀ n).ae_eq_mk.symm
  let A : Ω → Prop := fun ω => IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) ∧
    ∀ n, η n ω = lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale n)
  have hgood : ∀ᵐ ω ∂P, A ω := hμ.and hηeq
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hgood)
  let ν : Ω → Measure ℂ := fun ω => if ω ∈ N then 0 else μ ω
  have hA (ω : Ω) (hω : ω ∉ N) : A ω := by
    by_contra hn
    exact hω (hNsub hn)
  have hloc (ω : Ω) : IsLocallyFiniteMeasure (ν ω) := by
    by_cases hω : ω ∈ N
    · simp only [ν, hω, ite_true]
      infer_instance
    · simpa only [ν, hω, ite_false] using (hA ω hω).1.isLocallyFiniteMeasure
  have hopen (U : Set ℂ) (hU : IsOpen U) : Measurable (fun ω => ν ω U) := by
    obtain ⟨f, hf, hfc, hmass⟩ := exists_open_mass_test_functions hU
    let K : Kernel (Measure ℂ) ℂ := ⟨id, measurable_id⟩
    let G : Ω → ℝ≥0∞ := fun ω => ⨆ i, Filter.liminf
      (fun n => ENNReal.ofReal (∫ z, f i z ∂(η n ω))) atTop
    have hG : Measurable G := by
      apply Measurable.iSup
      intro i
      apply Measurable.liminf
      intro n
      exact (((hf i).stronglyMeasurable.integral_kernel (κ := K)).measurable.comp (hη n)).ennreal_ofReal
    have heq : (fun ω => ν ω U) = (fun ω => if ω ∈ N then 0 else G ω) := by
      funext ω
      by_cases hω : ω ∈ N
      · simp only [ν, hω, ite_true, Measure.coe_zero, Pi.zero_apply]
      · have ha := hA ω hω
        simp only [ν, hω, ite_false]
        rw [hmass (μ ω) ha.1.isLocallyFiniteMeasure]
        congr 1
        funext i
        apply (Filter.Tendsto.liminf_eq _).symm
        apply (ENNReal.continuous_ofReal.tendsto _).comp
        simpa only [ha.2] using ha.1.tendsto_integral (f i) (hf i) (hfc i)
    rw [heq]
    exact Measurable.ite hNmeas measurable_const hG
  have hν := measurable_measure_of_isOpen hloc hopen
  apply hν.aemeasurable.congr
  have hae : ∀ᵐ ω ∂P, ω ∉ N := ae_iff.mpr (by simpa using hNnull)
  filter_upwards [hae] with ω hω
  simp only [ν, hω, ite_false]

/-- The law of an almost surely locally finite random measure is determined
by the joint laws of its masses on finite families of open sets. -/
theorem identDistrib_of_open_masses {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {X Y : Ω → Measure ℂ}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hXloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (X ω))
    (hYloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Y ω))
    (hopen : ∀ (ι : Type) [Fintype ι] (U : ι → Set ℂ), (∀ i, IsOpen (U i)) →
      IdentDistrib (fun ω i => X ω (U i)) (fun ω i => Y ω (U i)) P P) :
    IdentDistrib X Y P P := by
  classical
  let O := {U : Set ℂ // IsOpen U}
  let F : Measure ℂ → O → ℝ≥0∞ := fun m U => m U.1
  have hF : Measurable F := Measurable.of_eval fun U => Measure.measurable_coe U.2.measurableSet
  have hd : IdentDistrib (F ∘ X) (F ∘ Y) P P := by
    apply (identDistrib_iff_forall_finset_identDistrib
      (hF.comp_aemeasurable hX) (hF.comp_aemeasurable hY)).2
    intro I
    convert hopen I (fun i => i.1.1) (fun i => i.1.2) using 1 <;> funext ω i <;> rfl
  let L := {m : Measure ℂ // IsLocallyFiniteMeasure m}
  let e : L → O → ℝ≥0∞ := fun m => F m.1
  let : MeasurableSpace L := MeasurableSpace.comap e inferInstance
  have hcoe : Measurable (Subtype.val : L → Measure ℂ) := by
    apply measurable_measure_of_isOpen (fun m => m.2)
    intro U hU
    exact (measurable_pi_apply (⟨U, hU⟩ : O)).comp (comap_measurable e)
  refine ⟨hX, hY, ?_⟩
  apply Measure.ext
  intro S hS
  obtain ⟨T, hT, heq⟩ := MeasurableSpace.measurableSet_comap.mp (hcoe hS)
  have hpreX : X ⁻¹' S =ᵐ[P] (F ∘ X) ⁻¹' T := by
    filter_upwards [hXloc] with ω hω
    change (X ω ∈ S) = (F (X ω) ∈ T)
    have hx := Set.ext_iff.mp heq (⟨X ω, hω⟩ : L)
    exact propext hx.symm
  have hpreY : Y ⁻¹' S =ᵐ[P] (F ∘ Y) ⁻¹' T := by
    filter_upwards [hYloc] with ω hω
    change (Y ω ∈ S) = (F (Y ω) ∈ T)
    have hy := Set.ext_iff.mp heq (⟨Y ω, hω⟩ : L)
    exact propext hy.symm
  rw [Measure.map_apply_of_aemeasurable hX hS, Measure.map_apply_of_aemeasurable hY hS,
    measure_congr hpreX, measure_congr hpreY, ← Measure.map_apply_of_aemeasurable hd.aemeasurable_fst hT,
    ← Measure.map_apply_of_aemeasurable hd.aemeasurable_snd hT, hd.map_eq]

/-- The normalized pullback of an LQG measure has the same law as the
original measure, assuming the staged affine-invariance and coordinate-change
inputs. -/
theorem IsWholePlaneGFF.identDistrib_normalizedPullback
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {k : ℝ} (hk : 0 < k) :
    IdentDistrib μ (fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) P P := by
  let _ := h.isGaussianProcess.isProbabilityMeasure
  have hscaled := isLQGMeasureOfField_normalizedPullback hCC h hγ hγ2 hα hμ hk
  have hs := hAff h (k : ℂ) (by exact_mod_cast hk.ne') 0
  have hsμ : IsLQGMeasureOfField P γ α₀
      (fun ω r z => hcirc ω (‖(k : ℂ)‖ * r) ((k : ℂ) * z + 0) - hcirc ω ‖(k : ℂ)‖ 0)
      (fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk, add_zero,
      Complex.real_smul] using hscaled
  apply identDistrib_of_open_masses (h.aemeasurable_lqgMeasure hμ) (hs.aemeasurable_lqgMeasure hsμ)
  · filter_upwards [hμ] with ω hω
    exact hω.isLocallyFiniteMeasure
  · filter_upwards [hscaled] with ω hω
    exact hω.isLocallyFiniteMeasure
  · intro ι _ U hU
    exact h.identDistrib_normalizedPullback_open_masses hAff hCC hγ hγ2 hα hμ hk U hU

/-- The cluster scale-invariance law for a fixed field, assuming pathwise
scaling, cluster-family measurability, and the two staged LQG inputs. -/
theorem clusterScaleInvariance_of_pathwise_and_measurable
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hscale : ClusterPathwiseScaleStep.{u}) (hmeas : ClusterFamilyMeasurabilityStep.{u})
    {k : ℝ} (hk : 0 < k) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    IdentDistrib (fun ω (t : Ioi (0 : ℝ)) => cluster (μ ω) 1 z t)
      (fun ω (t : Ioi (0 : ℝ)) => k⁻¹ • cluster (μ ω) k (k • z)
        (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0)) * t)) P P := by
  have hd := (h.identDistrib_normalizedPullback hAff hCC hγ hγ2 hα hμ hk).comp_of_aemeasurable
    (hmeas γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ z hz)
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [hscale γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ k hk] with ω hω
  funext t
  exact hω z hz t t.property

end HarmonicBalls
