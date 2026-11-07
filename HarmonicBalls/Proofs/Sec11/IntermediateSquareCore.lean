import HarmonicBalls.Proofs.Sec11.DyadicIntermediateSeed

/-! # Compact core obtained by removing square interiors -/

namespace HarmonicBalls
open Set

/-- Removing the interiors of pairwise disjoint closed proper pieces from a
compact set gives a compact core. Each piece meets the core along its boundary,
and smaller pieces lying in their interiors are disjoint from the core. -/
theorem compact_core_of_disjoint_closed_pieces {α ι : Type*}
    [TopologicalSpace α] [PreconnectedSpace α]
    (K : Set α) (H S : ι → Set α) (hK : IsCompact K)
    (hclosed : ∀ i, IsClosed (H i)) (hnonempty : ∀ i, (H i).Nonempty)
    (hproper : ∀ i, H i ≠ univ) (hHK : ∀ i, H i ⊆ K)
    (hdisj : ∀ i j, i ≠ j → Disjoint (H i) (H j))
    (hSH : ∀ i, S i ⊆ interior (H i)) :
    IsCompact (K \ ⋃ i, interior (H i)) ∧
    (∀ x ∈ K, x ∈ K \ ⋃ i, interior (H i) ∨ ∃ i, x ∈ H i) ∧
    (∀ i, (H i ∩ (K \ ⋃ j, interior (H j))).Nonempty) ∧
    Disjoint (⋃ i, S i) (K \ ⋃ i, interior (H i)) := by
  classical
  refine ⟨hK.diff (isOpen_iUnion fun _ => isOpen_interior), ?_, ?_, ?_⟩
  · intro x hx
    by_cases h : x ∈ ⋃ i, interior (H i)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp h
      exact Or.inr ⟨i, interior_subset hi⟩
    · exact Or.inl ⟨hx, h⟩
  · intro i
    obtain ⟨x, hx⟩ := nonempty_frontier_iff.mpr ⟨hnonempty i, hproper i⟩
    have hxH : x ∈ H i := (hclosed i).closure_eq ▸ hx.1
    have hxnot : x ∉ interior (H i) := hx.2
    refine ⟨x, hxH, hHK i hxH, ?_⟩
    intro hxunion
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxunion
    by_cases hij : i = j
    · subst j
      exact hxnot hj
    · exact Set.disjoint_left.mp (hdisj i j hij) hxH (interior_subset hj)
  · apply disjoint_left.mpr
    intro x hx hcore
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hcore.2 (mem_iUnion.mpr ⟨i, hSH i hi⟩)

/-- Intermediate squares of positive side have points both inside and outside. -/
theorem intermediateGridSquare_nonempty_ne_univ {N : ℕ} (a : ℂ) (r : ℝ)
    (hr : 0 < r) (i : Fin N × Fin N) :
    (complexIntermediateGridSquare a r i).Nonempty ∧
      complexIntermediateGridSquare a r i ≠ univ := by
  constructor
  · refine ⟨⟨a.re + (i.1.val : ℝ) * r, a.im + (i.2.val : ℝ) * r⟩, ?_⟩
    change ((i.1.val : ℝ) - 1 / 4) * r ≤
        (a.re + (i.1.val : ℝ) * r) - a.re ∧
      (a.re + (i.1.val : ℝ) * r) - a.re ≤ ((i.1.val : ℝ) + 5 / 4) * r ∧
      ((i.2.val : ℝ) - 1 / 4) * r ≤ (a.im + (i.2.val : ℝ) * r) - a.im ∧
      (a.im + (i.2.val : ℝ) * r) - a.im ≤ ((i.2.val : ℝ) + 5 / 4) * r
    constructor <;> [nlinarith; constructor <;> [nlinarith; constructor <;> nlinarith]]
  · intro heq
    have hx : (⟨a.re + ((i.1.val : ℝ) + 2) * r, a.im⟩ : ℂ) ∈
        complexIntermediateGridSquare a r i := by rw [heq]; trivial
    change ((i.1.val : ℝ) - 1 / 4) * r ≤
        (a.re + ((i.1.val : ℝ) + 2) * r) - a.re ∧
      (a.re + ((i.1.val : ℝ) + 2) * r) - a.re ≤ ((i.1.val : ℝ) + 5 / 4) * r ∧
      _ at hx
    nlinarith [hx.2.1]

/-- The intermediate squares of one parity class give a compact core whose
pieces are attached along their boundaries and whose protected mass tiles are
disjoint from the core. -/
theorem dyadic_intermediate_compact_core {N : ℕ} (a : ℂ) (r : ℝ) (hr : 0 < r)
    (j : Fin 4) (K : Set ℂ) (hK : IsCompact K)
    (hHK : ∀ i : {i : Fin N × Fin N // squareParity i = j},
      complexIntermediateGridSquare a r i.1 ⊆ K) :
    let H := fun i : {i : Fin N × Fin N // squareParity i = j} =>
      complexIntermediateGridSquare a r i.1
    let S := fun i : {i : Fin N × Fin N // squareParity i = j} =>
      complexGridSquare a r i.1
    IsCompact (K \ ⋃ i, interior (H i)) ∧
      (∀ x ∈ K, x ∈ K \ ⋃ i, interior (H i) ∨ ∃ i, x ∈ H i) ∧
      (∀ i, (H i ∩ (K \ ⋃ j, interior (H j))).Nonempty) ∧
      Disjoint (⋃ i, S i) (K \ ⋃ i, interior (H i)) := by
  apply compact_core_of_disjoint_closed_pieces _ _ _ hK
  · intro i
    exact isClosed_complexIntermediateGridSquare a r i.1
  · intro i
    exact (intermediateGridSquare_nonempty_ne_univ a r hr i.1).1
  · intro i
    exact (intermediateGridSquare_nonempty_ne_univ a r hr i.1).2
  · exact hHK
  · intro i k hik
    have hne : i.1 ≠ k.1 := fun h => hik (Subtype.ext h)
    exact (complex_enlarged_grid_squares_disjoint a r hr i.1 k.1
      (i.2.trans k.2.symm) hne).mono
      ((complexIntermediateGridSquare_subset_open_enlarged a r hr i.1).trans
        (complexOpenEnlargedGridSquare_subset a r i.1))
      ((complexIntermediateGridSquare_subset_open_enlarged a r hr k.1).trans
        (complexOpenEnlargedGridSquare_subset a r k.1))
  · intro i
    exact complexGridSquare_subset_interior_intermediate a r hr i.1

#print axioms compact_core_of_disjoint_closed_pieces
#print axioms dyadic_intermediate_compact_core
end HarmonicBalls
