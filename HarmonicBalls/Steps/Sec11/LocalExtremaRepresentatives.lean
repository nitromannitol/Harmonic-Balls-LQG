import HarmonicBalls.Steps.Sec11.InternalMetricMeasurable

/-! # Local representatives of random extrema -/

namespace HarmonicBalls

open Set MeasureTheory Topology TopologicalSpace Filter
open scoped ENNReal

/-- A random continuous section has a locally measurable supremum
representative when its values have a common almost-sure representative. -/
theorem exists_measurable_iSup_representative
    {Ω ι : Type*} [MeasurableSpace Ω] [TopologicalSpace ι] [SeparableSpace ι]
    (P : Measure Ω) (m : MeasurableSpace Ω) (F G : Ω → ι → ℝ≥0∞)
    (hG : ∀ i, Measurable[m] fun ω => G ω i)
    (hEq : ∀ᵐ ω ∂P, ∀ i, F ω i = G ω i)
    (hcont : ∀ᵐ ω ∂P, Continuous (F ω)) :
    ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧ ∀ᵐ ω ∂P, (⨆ i, F ω i) = Y ω := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ι
  let : Countable S := hSc.to_subtype
  refine ⟨fun ω => ⨆ i : S, G ω i, ?_, ?_⟩
  · let : MeasurableSpace Ω := m
    exact Measurable.iSup fun i : S => hG i
  · filter_upwards [hEq, hcont] with ω heq hc
    rw [← hSd.ciSup hc (show BddAbove (range (F ω)) from ⟨⊤, fun _ _ => le_top⟩)]
    exact iSup_congr fun i => heq i

/-- The corresponding result for infima. -/
theorem exists_measurable_iInf_representative
    {Ω ι : Type*} [MeasurableSpace Ω] [TopologicalSpace ι] [SeparableSpace ι]
    (P : Measure Ω) (m : MeasurableSpace Ω) (F G : Ω → ι → ℝ≥0∞)
    (hG : ∀ i, Measurable[m] fun ω => G ω i)
    (hEq : ∀ᵐ ω ∂P, ∀ i, F ω i = G ω i)
    (hcont : ∀ᵐ ω ∂P, Continuous (F ω)) :
    ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧ ∀ᵐ ω ∂P, (⨅ i, F ω i) = Y ω := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ι
  let : Countable S := hSc.to_subtype
  refine ⟨fun ω => ⨅ i : S, G ω i, ?_, ?_⟩
  · let : MeasurableSpace Ω := m
    exact Measurable.iInf fun i : S => hG i
  · filter_upwards [hEq, hcont] with ω heq hc
    rw [← hSd.ciInf hc (show BddBelow (range (F ω)) from ⟨⊥, fun _ _ => bot_le⟩)]
    exact iInf_congr fun i => heq i

/-- A lower semicontinuous random section has a local supremum representative,
even when the pointwise representatives agree only at each point separately. -/
theorem exists_measurable_iSup_representative_of_lowerSemicontinuous
    {Ω ι : Type*} [MeasurableSpace Ω] [TopologicalSpace ι] [SeparableSpace ι]
    (P : Measure Ω) (m : MeasurableSpace Ω) (F G : Ω → ι → ℝ≥0∞)
    (hG : ∀ i, Measurable[m] fun ω => G ω i)
    (hEq : ∀ i, ∀ᵐ ω ∂P, F ω i = G ω i)
    (hcont : ∀ᵐ ω ∂P, LowerSemicontinuous (F ω)) :
    ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧ ∀ᵐ ω ∂P, (⨆ i, F ω i) = Y ω := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ι
  let : Countable S := hSc.to_subtype
  refine ⟨fun ω => ⨆ i : S, G ω i, ?_, ?_⟩
  · let : MeasurableSpace Ω := m
    exact Measurable.iSup fun i : S => hG i
  · filter_upwards [ae_all_iff.mpr (fun i : S => hEq i), hcont] with ω heq hc
    have hdense : (⨆ i, F ω i) = ⨆ i : S, F ω i := by
      apply le_antisymm
      · apply iSup_le
        intro i
        apply le_of_forall_lt
        intro c hci
        obtain ⟨v, hv, hv'⟩ := eventually_iff_exists_mem.1 (hc i c hci)
        have hj := hSd.inter_nhds_nonempty hv
        exact lt_of_lt_of_le (hv' _ (mem_of_mem_inter_right hj.some_mem))
          (le_iSup (fun j : S => F ω j) ⟨hj.some, mem_of_mem_inter_left hj.some_mem⟩)
      · exact iSup_le fun i => le_iSup (F ω) i
    rw [hdense]
    exact iSup_congr heq

/-- Supremum of internal distances has a local measurable representative. -/
theorem exists_local_iSup_internalMetric_representative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {m : MeasurableSpace Ω}
    {D : Ω → ℂ → ℂ → ℝ} {G : Ω → ℂ → ℂ → ℝ≥0∞}
    {V A B : Set ℂ} (hV : IsOpen V) (hA : A ⊆ V) (hB : B ⊆ V)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hG : ∀ x ∈ A, ∀ y ∈ B, Measurable[m] fun ω => G ω x y)
    (hEq : ∀ᵐ ω ∂P, ∀ x ∈ A, ∀ y ∈ B, internalMetric (D ω) V x y = G ω x y) :
    ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧
      ∀ᵐ ω ∂P, (⨆ x ∈ A, ⨆ y ∈ B, internalMetric (D ω) V x y) = Y ω := by
  let F : Ω → A × B → ℝ≥0∞ := fun ω p => internalMetric (D ω) V p.1 p.2
  let H : Ω → A × B → ℝ≥0∞ := fun ω p => G ω p.1 p.2
  have hcont : ∀ᵐ ω ∂P, Continuous (F ω) := by
    filter_upwards [hmetric] with ω hω
    have hnonneg (a b : ℂ) : 0 ≤ D ω a b := by
      have ht := hω.triangle a b a
      rw [hω.self_eq_zero, hω.symm b a] at ht
      linarith
    have hc : Continuous (fun p : A × B => ((p.1 : ℂ), (p.2 : ℂ))) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact hω.continuousOn_internalMetric_pair hnonneg hV |>.comp_continuous hc
      (fun p => ⟨hA p.1.property, hB p.2.property⟩)
  obtain ⟨Y, hY, hYeq⟩ := @exists_measurable_iSup_representative Ω (A × B) mΩ inferInstance inferInstance P m F H
    (fun p => hG p.1 p.1.property p.2 p.2.property)
    (hEq.mono fun _ h p => h p.1 p.1.property p.2 p.2.property) hcont
  refine ⟨Y, hY, ?_⟩
  filter_upwards [hYeq] with ω hω
  simpa only [F, iSup_prod, iSup_subtype] using hω

/-- Infimum of internal distances has a local measurable representative. -/
theorem exists_local_iInf_internalMetric_representative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {m : MeasurableSpace Ω}
    {D : Ω → ℂ → ℂ → ℝ} {G : Ω → ℂ → ℂ → ℝ≥0∞}
    {V A B : Set ℂ} (hV : IsOpen V) (hA : A ⊆ V) (hB : B ⊆ V)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hG : ∀ x ∈ A, ∀ y ∈ B, Measurable[m] fun ω => G ω x y)
    (hEq : ∀ᵐ ω ∂P, ∀ x ∈ A, ∀ y ∈ B, internalMetric (D ω) V x y = G ω x y) :
    ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧
      ∀ᵐ ω ∂P, (⨅ x ∈ A, ⨅ y ∈ B, internalMetric (D ω) V x y) = Y ω := by
  let F : Ω → A × B → ℝ≥0∞ := fun ω p => internalMetric (D ω) V p.1 p.2
  let H : Ω → A × B → ℝ≥0∞ := fun ω p => G ω p.1 p.2
  have hcont : ∀ᵐ ω ∂P, Continuous (F ω) := by
    filter_upwards [hmetric] with ω hω
    have hnonneg (a b : ℂ) : 0 ≤ D ω a b := by
      have ht := hω.triangle a b a
      rw [hω.self_eq_zero, hω.symm b a] at ht
      linarith
    have hc : Continuous (fun p : A × B => ((p.1 : ℂ), (p.2 : ℂ))) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact hω.continuousOn_internalMetric_pair hnonneg hV |>.comp_continuous hc
      (fun p => ⟨hA p.1.property, hB p.2.property⟩)
  obtain ⟨Y, hY, hYeq⟩ := @exists_measurable_iInf_representative Ω (A × B) mΩ inferInstance inferInstance P m F H
    (fun p => hG p.1 p.1.property p.2 p.2.property)
    (hEq.mono fun _ h p => h p.1 p.1.property p.2 p.2.property) hcont
  refine ⟨Y, hY, ?_⟩
  filter_upwards [hYeq] with ω hω
  simpa only [F, iInf_prod, iInf_subtype] using hω

end HarmonicBalls
