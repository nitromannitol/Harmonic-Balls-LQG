import HarmonicBalls.FirstPass.S11c.UpperProb

/-!
# Proposition 11.10, the positivity of an intersection of events (fp-S11c, owner n1)

FIRST-PASS NEW (measure theory). In the probability step of the proof of Proposition 11.10 (paper lines 3091-3112), the class
event `X` (positive probability), the good set `G` (from the class choice), the piece event `A` (inner event of the small
cells) and the exterior event `B` (measurable exterior bound) are intersected. If the complements of the three good events have
total measure less than that of `X`, the intersection has positive measure. This is the elementary inequality used there.
-/

open MeasureTheory Set

namespace HarmonicBalls

/-- If `P Gᶜ + P Aᶜ + P Bᶜ < P X`, then `X ∩ G ∩ A ∩ B` has positive measure. -/
lemma measure_pos_inter_three_of_compl_sum_lt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X G A B : Set Ω} (hsum : P Gᶜ + P Aᶜ + P Bᶜ < P X) :
    0 < P (X ∩ G ∩ A ∩ B) := by
  by_contra h
  have h0 : P (X ∩ G ∩ A ∩ B) = 0 := le_zero_iff.1 (not_lt.1 h)
  have hsub : X ⊆ (X ∩ G ∩ A ∩ B) ∪ Gᶜ ∪ Aᶜ ∪ Bᶜ := by
    intro ω hω
    by_cases hG : ω ∈ G
    · by_cases hA : ω ∈ A
      · by_cases hB : ω ∈ B
        · exact Or.inl (Or.inl (Or.inl ⟨⟨⟨hω, hG⟩, hA⟩, hB⟩))
        · exact Or.inr hB
      · exact Or.inl (Or.inr hA)
    · exact Or.inl (Or.inl (Or.inr hG))
  have h2 : P X ≤ P Gᶜ + P Aᶜ + P Bᶜ :=
    calc P X ≤ P ((X ∩ G ∩ A ∩ B) ∪ Gᶜ ∪ Aᶜ ∪ Bᶜ) := measure_mono hsub
      _ ≤ P ((X ∩ G ∩ A ∩ B) ∪ Gᶜ ∪ Aᶜ) + P Bᶜ := measure_union_le _ _
      _ ≤ (P ((X ∩ G ∩ A ∩ B) ∪ Gᶜ) + P Aᶜ) + P Bᶜ := by
          gcongr
          exact measure_union_le _ _
      _ ≤ ((P (X ∩ G ∩ A ∩ B) + P Gᶜ) + P Aᶜ) + P Bᶜ := by
          gcongr
          exact measure_union_le _ _
      _ = P Gᶜ + P Aᶜ + P Bᶜ := by rw [h0]; ring
  exact absurd hsum (not_lt.2 h2)

end HarmonicBalls
