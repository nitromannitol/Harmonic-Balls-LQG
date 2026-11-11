import HarmonicBalls.Draft.Section11

/-!
# Lemma 11.17, Step 17.3: a truncation selection

Pure measure theory used in Step 17.3:
if an event `A` of positive probability is covered, up to a null set `N`, by a countable family `G n`, then some
`G n` meets `A` in a set of positive probability. In the proof of corrected Lemma 11.17 (paper lines 3355-3357) the
family is `G n = {a₂ ≥ 1/(n+1), d₂ ≤ n+1}` and `A = Ẽ₁ ∩ Ẽ₂(M)`; the covering by the `G n` up to a null set is
the almost-sure finiteness and positivity of `d₂` and `a₂` (proved separately).
-/

open MeasureTheory Set

namespace HarmonicBalls

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Countable selection: if `P A > 0` and `A ⊆ (⋃ n, G n) ∪ N` with `P N = 0`, then `P (A ∩ G n) > 0` for some `n`. -/
theorem exists_pos_inter_of_ae_cover {P : Measure Ω} {A : Set Ω} (hA : 0 < P A) {G : ℕ → Set Ω} {N : Set Ω}
    (hN : P N = 0) (hcov : A ⊆ (⋃ n, G n) ∪ N) : ∃ n, 0 < P (A ∩ G n) := by
  by_contra h
  have hnull : ∀ n, P (A ∩ G n) = 0 := fun n =>
    le_antisymm (not_lt.1 fun hn => h ⟨n, hn⟩) zero_le
  have hsub : A ⊆ (⋃ n, A ∩ G n) ∪ N := fun ω hω => by
    rcases hcov hω with h1 | h1
    · obtain ⟨n, hn⟩ := mem_iUnion.1 h1
      exact Or.inl (mem_iUnion.2 ⟨n, hω, hn⟩)
    · exact Or.inr h1
  have h0 : P ((⋃ n, A ∩ G n) ∪ N) = 0 := measure_union_null (measure_iUnion_null hnull) hN
  exact absurd ((measure_mono hsub).trans h0.le) (not_le.2 hA)

end HarmonicBalls
