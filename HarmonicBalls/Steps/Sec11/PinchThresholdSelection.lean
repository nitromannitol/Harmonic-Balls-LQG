import HarmonicBalls.Draft.Section11

/-! # Deterministic threshold selection on a positive-mass event

This is the countable selection needed before imposing strict auxiliary pinch
margins. No independence or conditional probability is asserted.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- On a positive-mass event where `f` is positive and `g` is finite, one can
choose deterministic positive lower and finite upper thresholds which hold
on a positive-mass subevent. Measurability is not required for this selection. -/
theorem exists_positive_measure_uniform_thresholds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (f g : Ω → ℝ≥0∞) (hA : 0 < P A)
    (hfg : ∀ ω ∈ A, f ω ≠ 0 ∧ g ω ≠ ∞) :
    ∃ n m : ℕ, 0 < n ∧
      0 < P {ω | ω ∈ A ∧ (n : ℝ≥0∞)⁻¹ < f ω ∧ g ω < (m : ℝ≥0∞)} := by
  let ι := {n : ℕ // 0 < n} × ℕ
  let E : ι → Set Ω := fun nm =>
    {ω | ω ∈ A ∧ ((nm.1 : ℕ) : ℝ≥0∞)⁻¹ < f ω ∧ g ω < (nm.2 : ℝ≥0∞)}
  have hcover : A ⊆ ⋃ i, E i := by
    intro ω hω
    obtain ⟨hf, hg⟩ := hfg ω hω
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hf
    have hnpos : 0 < n := by
      by_contra h
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos h
      subst n
      simp only [Nat.cast_zero, ENNReal.inv_zero, not_top_lt] at hn
    obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hg
    exact mem_iUnion.mpr ⟨(⟨n, hnpos⟩, m), hω, hn, hm⟩
  have hunion : 0 < P (⋃ i, E i) := hA.trans_le (measure_mono hcover)
  obtain ⟨⟨n, m⟩, hnm⟩ := exists_measure_pos_of_not_measure_iUnion_null hunion.ne'
  exact ⟨n, m, n.property, hnm⟩

/-- If the event and the random quantities are measurable, the selected
positive-mass event is measurable as well. -/
theorem exists_measurable_positive_measure_uniform_thresholds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (f g : Ω → ℝ≥0∞) (hAm : MeasurableSet A) (hf : Measurable f) (hg : Measurable g)
    (hA : 0 < P A) (hfg : ∀ ω ∈ A, f ω ≠ 0 ∧ g ω ≠ ∞) :
    ∃ n m : ℕ, 0 < n ∧ ∃ B ⊆
      {ω | ω ∈ A ∧ (n : ℝ≥0∞)⁻¹ < f ω ∧ g ω < (m : ℝ≥0∞)},
      MeasurableSet B ∧ 0 < P B := by
  obtain ⟨n, m, hn, hpos⟩ := exists_positive_measure_uniform_thresholds P A f g hA hfg
  refine ⟨n, m, hn, _, Subset.rfl, ?_, hpos⟩
  exact hAm.inter ((measurableSet_lt measurable_const hf).inter
    (measurableSet_lt hg measurable_const))

end HarmonicBalls
