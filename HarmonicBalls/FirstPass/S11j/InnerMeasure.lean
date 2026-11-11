import HarmonicBalls.FirstPass.S11j.Positivity

/-!
# Section 11: inner-measure form of a null-measurable event

The Lean statements of Lemmas 11.15-11.17 are in inner-measure form: `∃ A ⊆ S, MeasurableSet A ∧ 0 < P A`. A
null-measurable event of positive probability has such a measurable subset of the same probability. Pure measure
theory; no LQG input.
-/

namespace HarmonicBalls

open MeasureTheory

/-- A null-measurable set of positive measure contains a measurable set of positive measure. -/
theorem exists_measurable_subset_pos_of_nullMeasurableSet {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {S : Set Ω} (hS : NullMeasurableSet S P) (hpos : 0 < P S) :
    ∃ A ⊆ S, MeasurableSet A ∧ 0 < P A := by
  obtain ⟨t, htm, hSt⟩ := hS
  have h0 : P (t \ S) = 0 := (ae_eq_set.1 hSt).2
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null h0
  refine ⟨t \ N, fun x hx => ?_, htm.diff hNm, ?_⟩
  · by_contra hxS
    exact hx.2 (hsub ⟨hx.1, hxS⟩)
  · have hPS : P S = P t := measure_congr hSt
    have hpt : 0 < P t := by rw [← hPS]; exact hpos
    have hcov : t ⊆ (t \ N) ∪ N := fun x hx => by
      by_cases hxN : x ∈ N
      · exact Or.inr hxN
      · exact Or.inl ⟨hx, hxN⟩
    have hle : P t ≤ P (t \ N) := by
      calc P t ≤ P ((t \ N) ∪ N) := measure_mono hcov
        _ ≤ P (t \ N) + P N := measure_union_le _ _
        _ = P (t \ N) := by rw [hN0, add_zero]
    exact lt_of_lt_of_le hpt hle


end HarmonicBalls
