import HarmonicBalls.Proofs.Sec8.GermConditionalKernel

/-! # Normalized restrictions from countable local ratio versions -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace HarmonicBalls

/-- A countable generating π-system of normalized mass ratios suffices for a
local measurable restriction, even when the π-system does not contain `univ`. -/
theorem exists_normalizedRestriction_version_of_ae_piSystem_ratios
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : @Measure Ω mΩ)
    [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (U : Set ℂ) (hU : MeasurableSet U)
    (hpositive : ∀ᵐ ω ∂P, μ ω U ≠ 0 ∧ μ ω U ≠ ∞)
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ V ∈ S, MeasurableSet V)
    (hversion : ∀ V ∈ S, ∃ Y : Ω → ℝ≥0∞,
      @Measurable Ω ℝ≥0∞ m _ Y ∧
        (fun ω => μ ω (V ∩ U) / μ ω U) =ᵐ[P] Y) :
    ∃ ν : Ω → Measure ℂ, @Measurable Ω (Measure ℂ) m _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) U := by
  let μ' := hμ.mk μ
  have hμeq : μ =ᵐ[P] μ' := hμ.ae_eq_mk
  have hprob : ∀ᵐ ω ∂P, IsProbabilityMeasure (normalizedRestriction (μ' ω) U) := by
    filter_upwards [hpositive, hμeq] with ω hp he
    refine ⟨?_⟩
    simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply_univ, ← he]
    exact ENNReal.inv_mul_cancel hp.1 hp.2
  let T : Set (Set ℂ) := insert univ S
  have hTgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom T := by
    apply le_antisymm
    · rw [hgen]
      exact MeasurableSpace.generateFrom_mono (subset_insert univ S)
    · apply MeasurableSpace.generateFrom_le
      intro V hV
      rcases Set.mem_insert_iff.mp hV with rfl | hV
      · exact MeasurableSet.univ
      · exact hsets V hV
  have hmass : ∀ V ∈ T, ∃ Y : Ω → ℝ≥0∞,
      @Measurable Ω ℝ≥0∞ m _ Y ∧
        (fun ω => normalizedRestriction (μ' ω) U V) =ᵐ[P] Y := by
    intro V hV
    rcases Set.mem_insert_iff.mp hV with rfl | hV
    · refine ⟨fun _ => 1, measurable_const, ?_⟩
      filter_upwards [hprob] with ω hp
      exact hp.measure_univ
    · obtain ⟨Y, hYm, hY⟩ := hversion V hV
      refine ⟨Y, hYm, ?_⟩
      filter_upwards [hμeq, hY] with ω he hy
      simpa only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
        Measure.restrict_apply (hsets V hV), ENNReal.div_eq_inv_mul, ← he] using hy
  obtain ⟨ν, hνm, hν⟩ := @exists_local_measure_version_of_piSystem Ω mΩ P _ m hm
    (fun ω => normalizedRestriction (μ' ω) U)
    ((measurable_normalizedRestriction_measure U hU).comp hμ.measurable_mk) hprob
    T (hcount.insert univ) hTgen hpi.insert_univ
    (by intro V hV; rcases Set.mem_insert_iff.mp hV with rfl | hV
        · exact MeasurableSet.univ
        · exact hsets V hV) (mem_insert univ S) hmass
  refine ⟨ν, hνm, ?_⟩
  filter_upwards [hν, hμeq] with ω hνω he
  simpa [← he] using hνω

/-- The countable π-system versions extend to normalized masses of every
Borel set. -/
theorem exists_ae_borel_ratio_version_of_piSystem_ratios
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : @Measure Ω mΩ)
    [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (U : Set ℂ) (hU : MeasurableSet U)
    (hpositive : ∀ᵐ ω ∂P, μ ω U ≠ 0 ∧ μ ω U ≠ ∞)
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ V ∈ S, MeasurableSet V)
    (hversion : ∀ V ∈ S, ∃ Y : Ω → ℝ≥0∞,
      @Measurable Ω ℝ≥0∞ m _ Y ∧
        (fun ω => μ ω (V ∩ U) / μ ω U) =ᵐ[P] Y)
    (A : Set ℂ) (hA : MeasurableSet A) :
    ∃ Y : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞ m _ Y ∧
      (fun ω => μ ω (A ∩ U) / μ ω U) =ᵐ[P] Y := by
  obtain ⟨ν, hνm, hν⟩ := @exists_normalizedRestriction_version_of_ae_piSystem_ratios
    Ω mΩ P _ m hm μ hμ U hU hpositive S hcount hgen hpi hsets hversion
  refine ⟨fun ω => ν ω A, (Measure.measurable_coe hA).comp hνm, ?_⟩
  filter_upwards [hν] with ω hνω
  have := congrArg (fun η : Measure ℂ => η A) hνω
  simpa only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hA, ENNReal.div_eq_inv_mul] using this.symm

end HarmonicBalls
