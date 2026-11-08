import HarmonicBalls.Proofs.Sec5.LQGApproxDecoder

/-! # Compact suprema of circle averages

Countable dense coordinates give measurable finite representatives of compact
suprema. The GFF and circle-average construction used here are due to Leonardo
Bonanno (LatticeProb).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter

/-- A continuous compact supremum has a measurable real-valued representative
when its fixed spatial coordinates are measurable. -/
theorem exists_measurable_compact_supremum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty)
    (f : Ω → ℂ → ℝ) (hm : ∀ z, Measurable (fun ω => f ω z))
    (hc : ∀ᵐ ω ∂P, Continuous (f ω)) :
    ∃ S : Ω → ℝ, Measurable S ∧
      ∀ᵐ ω ∂P, S ω = sSup (f ω '' K) := by
  classical
  obtain ⟨D, hDc, hDK, hKD⟩ := TopologicalSpace.exists_countable_dense_subset K
  let S : Ω → ℝ := fun ω => sSup (f ω '' D)
  have hSm : Measurable S := Measurable.sSup hDc (fun z _ => hm z)
  refine ⟨S, hSm, ?_⟩
  filter_upwards [hc] with ω hω
  have hDb : BddAbove (f ω '' D) := (hK.bddAbove_image hω.continuousOn).mono
    (Set.image_mono hDK)
  have hDn : D.Nonempty := by
    by_contra h
    have : D = ∅ := not_nonempty_iff_eq_empty.mp h
    simp only [this, closure_empty, subset_empty_iff] at hKD
    exact hne.ne_empty hKD
  apply le_antisymm
  · apply csSup_le (hDn.image _)
    rintro _ ⟨z, hz, rfl⟩
    exact le_csSup (hK.bddAbove_image hω.continuousOn) (mem_image_of_mem _ (hDK hz))
  · apply csSup_le (hne.image _)
    rintro _ ⟨z, hz, rfl⟩
    have hclosed : IsClosed {x : ℂ | f ω x ≤ S ω} :=
      isClosed_le hω continuous_const
    have hsub : D ⊆ {x : ℂ | f ω x ≤ S ω} := by
      intro x hx
      exact le_csSup hDb (mem_image_of_mem _ hx)
    exact closure_minimal hsub hclosed (hKD hz)

/-- A fixed-radius circle-average supremum over a nonempty closed ball has a
measurable real-valued representative. -/
theorem IsWholePlaneGFF.exists_measurable_fieldCircleAverage_supremum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (α : ℝ) {L R : ℝ} (hL : 0 < L)
    (hR : 0 ≤ R) (a : ℂ) :
    ∃ S : Ω → ℝ, Measurable S ∧ ∀ᵐ ω ∂P,
      S ω = sSup ((fun z => fieldCircleAverage α (hcirc ω) L z) '' closedBall a R) := by
  apply exists_measurable_compact_supremum (closedBall a R) (isCompact_closedBall _ _)
    ⟨a, mem_closedBall_self hR⟩
  · intro z
    exact (h.measurable_circle L z hL).sub measurable_const
  · exact h.ae_continuous_fieldCircleAverage α hL

/-- A positive measurable representative of the exponential of the compact
circle-average supremum. -/
theorem IsWholePlaneGFF.exists_measurable_exp_fieldCircleAverage_supremum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (α : ℝ) {L R : ℝ} (hL : 0 < L)
    (hR : 0 ≤ R) (a : ℂ) :
    ∃ T : Ω → ℝ, Measurable T ∧ (∀ ω, 0 < T ω) ∧ ∀ᵐ ω ∂P,
      T ω = Real.exp (sSup ((fun z => fieldCircleAverage α (hcirc ω) L z) '' closedBall a R)) := by
  obtain ⟨S, hS, heq⟩ := h.exists_measurable_fieldCircleAverage_supremum α hL hR a
  refine ⟨fun ω => Real.exp (S ω), hS.exp, fun ω => Real.exp_pos _, ?_⟩
  filter_upwards [heq] with ω hω
  rw [hω]

/-- The compact supremum of the exponential of any real multiple of the
circle field has a positive measurable representative. -/
theorem IsWholePlaneGFF.exists_measurable_exp_mul_fieldCircleAverage_supremum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (α ξ : ℝ) {L R : ℝ} (hL : 0 < L)
    (hR : 0 ≤ R) (a : ℂ) :
    ∃ T : Ω → ℝ, Measurable T ∧ (∀ ω, 0 < T ω) ∧ ∀ᵐ ω ∂P,
      T ω = sSup ((fun z => Real.exp (ξ * fieldCircleAverage α (hcirc ω) L z)) ''
        closedBall a R) := by
  let K := closedBall a R
  have hK : IsCompact K := isCompact_closedBall _ _
  have hne : K.Nonempty := ⟨a, mem_closedBall_self hR⟩
  have hcont : ∀ᵐ ω ∂P,
      Continuous (fun z => ξ * fieldCircleAverage α (hcirc ω) L z) := by
    filter_upwards [h.ae_continuous_fieldCircleAverage α hL] with ω hω
    exact continuous_const.mul hω
  obtain ⟨S, hS, heq⟩ := exists_measurable_compact_supremum K hK hne
    (fun ω z => ξ * fieldCircleAverage α (hcirc ω) L z)
    (fun z => ((h.measurable_circle L z hL).sub measurable_const).const_mul ξ) hcont
  refine ⟨fun ω => Real.exp (S ω), hS.exp, fun ω => Real.exp_pos _, ?_⟩
  filter_upwards [heq, hcont] with ω hω hcω
  rw [hω]
  let f : ℂ → ℝ := fun z => ξ * fieldCircleAverage α (hcirc ω) L z
  have hfb : BddAbove (f '' K) := hK.bddAbove_image hcω.continuousOn
  have hexb : BddAbove ((fun z => Real.exp (f z)) '' K) :=
    hK.bddAbove_image (Real.continuous_exp.comp hcω).continuousOn
  obtain ⟨z, hz, hzmax⟩ := hK.exists_sSup_image_eq hne hcω.continuousOn
  change Real.exp (sSup (f '' K)) = sSup ((fun z => Real.exp (f z)) '' K)
  apply le_antisymm
  · rw [hzmax]
    exact le_csSup hexb (mem_image_of_mem _ hz)
  · apply csSup_le (hne.image _)
    rintro _ ⟨x, hx, rfl⟩
    exact Real.exp_le_exp.mpr (le_csSup hfb (mem_image_of_mem _ hx))

#print axioms exists_measurable_compact_supremum
#print axioms IsWholePlaneGFF.exists_measurable_fieldCircleAverage_supremum
#print axioms IsWholePlaneGFF.exists_measurable_exp_fieldCircleAverage_supremum
#print axioms IsWholePlaneGFF.exists_measurable_exp_mul_fieldCircleAverage_supremum

end HarmonicBalls
