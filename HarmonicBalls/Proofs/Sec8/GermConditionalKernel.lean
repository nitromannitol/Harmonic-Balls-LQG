import HarmonicBalls.Proofs.Sec8.AEMassRatioRepresentatives
import HarmonicBalls.Proofs.Sec8.MeasurableStartingAtoms
import Mathlib.Probability.Kernel.CondDistrib

/-! # Conditional kernels over a local sigma-algebra -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace HarmonicBalls

/-- A probability kernel has a conditional version on a smaller sigma-algebra,
characterized by its integrals over local events. -/
theorem exists_local_conditionalKernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : @Measure Ω mΩ)
    [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (κ : @Kernel Ω ℂ mΩ _) [IsMarkovKernel κ] :
    ∃ κ' : @Kernel Ω ℂ m _, IsMarkovKernel κ' ∧ ∀ (A : Set Ω) (V : Set ℂ),
      MeasurableSet[m] A → MeasurableSet V →
      ∫⁻ ω in A, κ' ω V ∂(P.trim hm) = ∫⁻ ω in A, κ ω V ∂P := by
  have hf : @Measurable (Ω × ℂ) Ω (mΩ.prod inferInstance) m Prod.fst :=
    (measurable_id'' hm).comp measurable_fst
  have hid : @Measurable (Ω × ℂ) (Ω × ℂ) (mΩ.prod inferInstance)
      (m.prod inferInstance) id := by
    simpa only [Function.id_def] using hf.prodMk measurable_snd
  let J : @Measure (Ω × ℂ) (m.prod inferInstance) := @Measure.map (Ω × ℂ) (Ω × ℂ) (mΩ.prod inferInstance)
    (m.prod inferInstance) id (P ⊗ₘ κ)
  have : IsFiniteMeasure J := Measure.isFiniteMeasure_map (P ⊗ₘ κ) id
  have hfst : J.fst = P.trim hm := by
    apply Measure.ext
    intro A hA
    rw [Measure.fst_apply hA, trim_measurableSet_eq hm hA]
    rw [Measure.map_apply hid (measurable_fst hA)]
    change (P ⊗ₘ κ) (Prod.fst ⁻¹' A) = P A
    have heq := congrArg (fun ν : @Measure Ω mΩ => ν A) (Measure.fst_compProd P κ)
    exact (@Measure.fst_apply Ω ℂ mΩ _ (P ⊗ₘ κ) A (hm A hA)).symm.trans heq
  refine ⟨J.condKernel, inferInstance, ?_⟩
  intro A V hA hV
  calc
    ∫⁻ ω in A, J.condKernel ω V ∂(P.trim hm) = J (A ×ˢ V) := by
      rw [← hfst]
      exact Measure.setLIntegral_condKernel_eq_measure_prod hA hV
    _ = (P ⊗ₘ κ) (A ×ˢ V) := by
      exact Measure.map_apply hid (hA.prod hV)
    _ = ∫⁻ ω in A, κ ω V ∂P := Measure.compProd_apply_prod (hm A hA) hV

/-- A Markov kernel has a local measurable version if its masses on a countable
    generating π-system have local measurable versions almost everywhere. -/
theorem exists_local_kernel_version_of_piSystem
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : @Measure Ω mΩ)
    [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (κ : @Kernel Ω ℂ mΩ _) [IsMarkovKernel κ]
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ V ∈ S, MeasurableSet V) (huniv : univ ∈ S)
    (hversion : ∀ V ∈ S, ∃ Y : Ω → ℝ≥0∞,
      @Measurable Ω ℝ≥0∞ m _ Y ∧ (fun ω => κ ω V) =ᵐ[P] Y) :
    ∃ ν : Ω → Measure ℂ, @Measurable Ω (Measure ℂ) m _ ν ∧
      ∀ᵐ ω ∂P, ν ω = κ ω := by
  obtain ⟨κ', hk', hconditional⟩ := @exists_local_conditionalKernel Ω mΩ P _ m hm κ _
  have : IsMarkovKernel κ' := hk'
  have heq : ∀ V ∈ S, (fun ω => κ' ω V) =ᵐ[P] (fun ω => κ ω V) := by
    intro V hV
    obtain ⟨Y, hYm, hYae⟩ := hversion V hV
    have htrim : (fun ω => κ' ω V) =ᵐ[P.trim hm] Y := by
      apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (κ'.measurable_coe (hsets V hV)) hYm
      intro A hA _
      calc
        ∫⁻ ω in A, κ' ω V ∂(P.trim hm) = ∫⁻ ω in A, κ ω V ∂P :=
          hconditional A V hA (hsets V hV)
        _ = ∫⁻ ω in A, Y ω ∂P := lintegral_congr_ae (ae_restrict_of_ae hYae)
        _ = ∫⁻ ω in A, Y ω ∂(P.trim hm) := (setLIntegral_trim hm hYm hA).symm
    exact (ae_eq_of_ae_eq_trim htrim).trans hYae.symm
  let : Countable S := hcount.to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ V ∈ S, κ' ω V = κ ω V := by
    have hh : ∀ v : S, ∀ᵐ ω ∂P, κ' ω v.1 = κ ω v.1 := fun v => heq v.1 v.2
    filter_upwards [ae_all_iff.mpr hh] with ω hω V hV
    exact hω ⟨V, hV⟩
  refine ⟨fun ω => κ' ω, ?_, ?_⟩
  · let : MeasurableSpace Ω := m
    exact Measurable.measure_of_isPiSystem hgen hpi
      (fun V hV => κ'.measurable_coe (hsets V hV)) (κ'.measurable_coe MeasurableSet.univ)
  · filter_upwards [hall] with ω hω
    exact ext_of_generate_finite S hgen hpi hω (hω univ huniv)

/-- Scalar almost-everywhere versions determine a local measure-valued version
for a measurable random probability measure. -/
theorem exists_local_measure_version_of_piSystem
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : @Measure Ω mΩ)
    [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (μ : Ω → Measure ℂ) (hμ : @Measurable Ω (Measure ℂ) mΩ _ μ)
    (hprob : ∀ᵐ ω ∂P, IsProbabilityMeasure (μ ω))
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ V ∈ S, MeasurableSet V) (huniv : univ ∈ S)
    (hversion : ∀ V ∈ S, ∃ Y : Ω → ℝ≥0∞,
      @Measurable Ω ℝ≥0∞ m _ Y ∧ (fun ω => μ ω V) =ᵐ[P] Y) :
    ∃ ν : Ω → Measure ℂ, @Measurable Ω (Measure ℂ) m _ ν ∧
      ∀ᵐ ω ∂P, ν ω = μ ω := by
  let κ : @Kernel Ω ℂ mΩ _ := @Kernel.mk Ω ℂ mΩ _ μ hμ
  obtain ⟨η, hη, hmarkov⟩ := κ.exists_ae_eq_isMarkovKernel hprob (IsProbabilityMeasure.ne_zero P)
  have : IsMarkovKernel η := hmarkov
  have hηversion : ∀ V ∈ S, ∃ Y : Ω → ℝ≥0∞,
      @Measurable Ω ℝ≥0∞ m _ Y ∧ (fun ω => η ω V) =ᵐ[P] Y := by
    intro V hV
    obtain ⟨Y, hYm, hY⟩ := hversion V hV
    refine ⟨Y, hYm, ?_⟩
    filter_upwards [hη, hY] with ω hηω hYω
    exact (congrArg (fun ν : Measure ℂ => ν V) hηω).symm.trans hYω
  obtain ⟨ν, hνm, hν⟩ := @exists_local_kernel_version_of_piSystem Ω mΩ P _ m hm η _
    S hcount hgen hpi hsets huniv hηversion
  refine ⟨ν, hνm, ?_⟩
  filter_upwards [hν, hη] with ω hνω hηω
  exact hνω.trans hηω.symm

/-- Ordinary almost-everywhere versions of the normalized masses on open sets
produce a local measure version, provided the original random measure is
measurable and the normalizing mass is almost surely nonzero and finite. -/
theorem exists_normalizedRestriction_version_of_ae_open_ratios
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : @Measure Ω mΩ)
    [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (μ : Ω → Measure ℂ) (hμ : @Measurable Ω (Measure ℂ) mΩ _ μ)
    (U : Set ℂ) (hU : MeasurableSet U)
    (hpositive : ∀ᵐ ω ∂P, μ ω U ≠ 0 ∧ μ ω U ≠ ∞)
    (hversion : ∀ V : Set ℂ, IsOpen V → ∃ Y : Ω → ℝ≥0∞,
      @Measurable Ω ℝ≥0∞ m _ Y ∧
        (fun ω => μ ω (V ∩ U) / μ ω U) =ᵐ[P] Y) :
    ∃ ν : Ω → Measure ℂ, @Measurable Ω (Measure ℂ) m _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) U := by
  obtain ⟨S, hcount, hpi, hopen, huniv, hgen⟩ := exists_countable_open_piSystem_complex
  have hprob : ∀ᵐ ω ∂P, IsProbabilityMeasure (normalizedRestriction (μ ω) U) := by
    filter_upwards [hpositive] with ω hω
    refine ⟨?_⟩
    simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hω.1 hω.2
  apply @exists_local_measure_version_of_piSystem Ω mΩ P _ m hm
    (fun ω => normalizedRestriction (μ ω) U)
    ((measurable_normalizedRestriction_measure U hU).comp hμ) hprob
    S hcount hgen hpi (fun V hV => (hopen V hV).measurableSet) huniv
  intro V hV
  obtain ⟨Y, hYm, hY⟩ := hversion V (hopen V hV)
  refine ⟨Y, hYm, ?_⟩
  simpa only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (hopen V hV).measurableSet, ENNReal.div_eq_inv_mul] using hY

/-- The same construction applies to an almost-everywhere measurable random
measure, allowing an arbitrary modification on a null set. -/
theorem exists_normalizedRestriction_version_of_aemeasurable_ae_open_ratios
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : @Measure Ω mΩ)
    [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (U : Set ℂ) (hU : MeasurableSet U)
    (hpositive : ∀ᵐ ω ∂P, μ ω U ≠ 0 ∧ μ ω U ≠ ∞)
    (hversion : ∀ V : Set ℂ, IsOpen V → ∃ Y : Ω → ℝ≥0∞,
      @Measurable Ω ℝ≥0∞ m _ Y ∧
        (fun ω => μ ω (V ∩ U) / μ ω U) =ᵐ[P] Y) :
    ∃ ν : Ω → Measure ℂ, @Measurable Ω (Measure ℂ) m _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) U := by
  let μ' := hμ.mk μ
  have hμeq : μ =ᵐ[P] μ' := hμ.ae_eq_mk
  have hpos' : ∀ᵐ ω ∂P, μ' ω U ≠ 0 ∧ μ' ω U ≠ ∞ := by
    filter_upwards [hpositive, hμeq] with ω hp he
    simpa [← he] using hp
  have hv' : ∀ V : Set ℂ, IsOpen V → ∃ Y : Ω → ℝ≥0∞,
      @Measurable Ω ℝ≥0∞ m _ Y ∧
        (fun ω => μ' ω (V ∩ U) / μ' ω U) =ᵐ[P] Y := by
    intro V hV
    obtain ⟨Y, hYm, hY⟩ := hversion V hV
    refine ⟨Y, hYm, ?_⟩
    filter_upwards [hμeq, hY] with ω he hy
    simpa [← he] using hy
  obtain ⟨ν, hνm, hν⟩ := @exists_normalizedRestriction_version_of_ae_open_ratios
    Ω mΩ P _ m hm μ' hμ.measurable_mk U hU hpos' hv'
  refine ⟨ν, hνm, ?_⟩
  filter_upwards [hν, hμeq] with ω hνω he
  simpa [← he] using hνω

end HarmonicBalls
