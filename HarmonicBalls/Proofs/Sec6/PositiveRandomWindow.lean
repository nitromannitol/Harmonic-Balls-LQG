import Mathlib

/-! # Positive finite random variables admit high-probability windows -/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- A positive real random variable lies in a deterministic compact positive
interval outside a set of arbitrarily small measure. -/
theorem exists_positive_window_of_ae_pos
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) (hpos : ∀ᵐ ω ∂P, 0 < X ω)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      P {ω | X ω ∉ Icc lo hi} ≤ δ := by
  let A : ℕ → Set Ω := fun n => {ω | X ω < 1 / (n + 1 : ℝ) ∨ (n + 1 : ℝ) < X ω}
  have hm (n : ℕ) : NullMeasurableSet (A n) P :=
    (nullMeasurableSet_lt hX aemeasurable_const).union
      (nullMeasurableSet_lt aemeasurable_const hX)
  have ha : Antitone A := by
    intro m n hmn ω hω
    have hden : (m + 1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.add_le_add_right hmn 1
    have hinv : 1 / (n + 1 : ℝ) ≤ 1 / (m + 1 : ℝ) :=
      one_div_le_one_div_of_le (by positivity) hden
    rcases hω with hlow | hhigh
    · exact Or.inl (lt_of_lt_of_le hlow hinv)
    · exact Or.inr (lt_of_le_of_lt hden hhigh)
  have hz : P (⋂ n, A n) = 0 := by
    apply measure_mono_null _ (ae_iff.1 hpos)
    intro ω hω hnot
    have hx : 0 < X ω := hnot
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt hx
    obtain ⟨j, hj⟩ := exists_nat_gt (X ω)
    have hb : ω ∈ A (max i j) := mem_iInter.1 hω _
    have hi' : 1 / (max i j + 1 : ℝ) ≤ 1 / (i + 1 : ℝ) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right (le_max_left i j) 1)
    have hj' : (j : ℝ) ≤ (max i j + 1 : ℝ) := by
      have h : (j : ℝ) ≤ (max i j : ℕ) := by exact_mod_cast le_max_right i j
      linarith
    rcases hb with h | h <;> linarith
  have hlim := tendsto_measure_iInter_atTop hm ha ⟨0, measure_ne_top P _⟩
  rw [hz] at hlim
  obtain ⟨n, hn⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_nhds hδ))
  refine ⟨1 / (n + 1 : ℝ), (n + 1 : ℝ), by positivity, by positivity, ?_⟩
  have hset : {ω | X ω ∉ Icc (1 / (n + 1 : ℝ)) (n + 1 : ℝ)} = A n := by
    ext ω
    simp only [A, mem_ofPred_eq, mem_Icc, not_and_or, not_le]
  rw [hset]
  exact (hn n le_rfl).le

/-- A positive finite extended-nonnegative random variable lies in a
deterministic positive finite window with arbitrarily high probability. -/
theorem exists_ennreal_window_of_ae_pos_ne_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {X : Ω → ℝ≥0∞} (hX : AEMeasurable X P)
    (hpos : ∀ᵐ ω ∂P, 0 < X ω ∧ X ω ≠ ∞)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      P {ω | X ω ∉ Icc (ENNReal.ofReal lo) (ENNReal.ofReal hi)} ≤ δ := by
  have hreal : ∀ᵐ ω ∂P, 0 < (X ω).toReal := by
    filter_upwards [hpos] with ω hω
    exact ENNReal.toReal_pos hω.1.ne' hω.2
  obtain ⟨lo, hi, hlo, hhi, hbound⟩ :=
    exists_positive_window_of_ae_pos P (ENNReal.measurable_toReal.comp_aemeasurable hX) hreal hδ
  refine ⟨lo, hi, hlo, hhi, ?_⟩
  refine (measure_mono_ae ?_).trans hbound
  filter_upwards [hpos] with ω hω hbad
  by_contra h
  have hh : (X ω).toReal ∈ Icc lo hi := h
  apply hbad
  constructor
  · have ht := ENNReal.ofReal_le_ofReal hh.1
    rw [ENNReal.ofReal_toReal hω.2] at ht
    exact ht
  · have ht := ENNReal.ofReal_le_ofReal hh.2
    rw [ENNReal.ofReal_toReal hω.2] at ht
    exact ht

end HarmonicBalls.Section6
