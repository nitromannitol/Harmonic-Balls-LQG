import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.ENNReal.Inv

/-!
# First pass, Section 11 thresholds for the third pinch event (fp-S11h, owner n2)

Step B of Lemma 11.17 (`lemma:third-event-proof`, corrected paper lines 3726-3756): "choose deterministic `c₁, c₂ > 0`
such that `F = E₁ ∩ E₂ ∩ {a₂ ≥ c₁, d₂ ≤ c₂}` has positive probability". This file is generic measure theory with no
input: if an event `X` has positive inner measure, and two quantities `a`, `d` are almost surely positive and finite
respectively (both almost everywhere measurable), then some pair of thresholds gives a measurable subevent of `X` of
positive probability. The quantities `a₂` (a setDist of disjoint compact sets) and `d₂` (an internal diameter) are
supplied by the caller, with their measurability and a.s. positivity and finiteness.
-/

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicBalls

/-- Continuity from below on the thresholds `c₁ = (n+1)⁻¹`, `c₂ = n+1`: a positive-inner-measure event `X`, on which
`0 < a` and `d < ∞` almost surely, contains a measurable subset of positive probability inside
`{c₁ ≤ a} ∩ {d ≤ c₂}` for some `n`. -/
theorem exists_measurable_thresholds_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Set Ω} (hX : ∃ A ⊆ X, MeasurableSet A ∧ 0 < P A)
    {a d : Ω → ℝ≥0∞} (ha : AEMeasurable a P) (hd : AEMeasurable d P)
    (hapos : ∀ᵐ ω ∂P, 0 < a ω) (hdfin : ∀ᵐ ω ∂P, d ω ≠ ∞) :
    ∃ c₁ c₂ : ℝ≥0∞, 0 < c₁ ∧ c₂ ≠ ∞ ∧
      ∃ A ⊆ X ∩ ({ω | c₁ ≤ a ω} ∩ {ω | d ω ≤ c₂}), MeasurableSet A ∧ 0 < P A := by
  obtain ⟨A0, hA0X, hA0, hA0pos⟩ := hX
  let c₁ : ℕ → ℝ≥0∞ := fun n => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹
  let c₂ : ℕ → ℝ≥0∞ := fun n => ((n + 1 : ℕ) : ℝ≥0∞)
  let T : ℕ → Set Ω := fun n => {ω | c₁ n ≤ a ω} ∩ {ω | d ω ≤ c₂ n}
  have hT : ∀ n, NullMeasurableSet (T n) P := by
    intro n
    exact (ha.nullMeasurableSet_preimage measurableSet_Ici).inter (hd.nullMeasurableSet_preimage measurableSet_Iic)
  have hcover : ∀ᵐ ω ∂P, ∃ n, ω ∈ T n := by
    filter_upwards [hapos, hdfin] with ω h1 h2
    obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt h1.ne'
    obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt h2
    refine ⟨max m k, ?_, ?_⟩
    · have hle : m ≤ max m k + 1 := le_trans (le_max_left m k) (Nat.le_succ _)
      exact (ENNReal.inv_le_inv.2 (by exact_mod_cast hle)).trans hm.le
    · have hle : k ≤ max m k + 1 := le_trans (le_max_right m k) (Nat.le_succ _)
      exact le_trans hk.le (by show ((k : ℕ) : ℝ≥0∞) ≤ ((max m k + 1 : ℕ) : ℝ≥0∞); exact_mod_cast hle)
  have hpiece : ∃ n, 0 < P (A0 ∩ T n) := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have h0 : ∀ n, P (A0 ∩ T n) = 0 := fun n => nonpos_iff_eq_zero.1 (hcon n)
    have hnull : P (⋃ n, A0 ∩ T n) = 0 := measure_iUnion_null h0
    have hN : P {ω | ¬ ∃ n, ω ∈ T n} = 0 := ae_iff.1 hcover
    have hsub : A0 ⊆ (⋃ n, A0 ∩ T n) ∪ {ω | ¬ ∃ n, ω ∈ T n} := by
      intro ω hω
      by_cases h : ∃ n, ω ∈ T n
      · obtain ⟨n, hn⟩ := h
        exact Or.inl (mem_iUnion.2 ⟨n, hω, hn⟩)
      · exact Or.inr h
    have hle : P A0 ≤ P (⋃ n, A0 ∩ T n) + P {ω | ¬ ∃ n, ω ∈ T n} :=
      (measure_mono hsub).trans (measure_union_le _ _)
    rw [hnull, hN, add_zero] at hle
    exact absurd (lt_of_lt_of_le hA0pos hle) (lt_irrefl _)
  obtain ⟨n, hn⟩ := hpiece
  have hB : NullMeasurableSet (A0 ∩ T n) P := hA0.nullMeasurableSet.inter (hT n)
  obtain ⟨A, hAsub, hAmeas, hAeq⟩ := hB.exists_measurable_subset_ae_eq
  refine ⟨c₁ n, c₂ n, ?_, ENNReal.natCast_ne_top _, A, ?_, hAmeas, ?_⟩
  · exact ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)
  · intro ω hω
    have hω' := hAsub hω
    exact ⟨hA0X hω'.1, hω'.2⟩
  · rw [measure_congr hAeq]
    exact hn

#print axioms exists_measurable_thresholds_pos

end HarmonicBalls
