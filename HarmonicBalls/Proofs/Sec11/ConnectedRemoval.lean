import HarmonicBalls.Proofs.Sec11.RectangleBoundary

/-! # Connectedness under removal of square interiors -/

namespace HarmonicBalls
open Set

/-- Removing the interior of a closed subset with preconnected frontier
preserves preconnectedness of the containing set. -/
theorem isPreconnected_sdiff_interior_of_frontier {α : Type*} [TopologicalSpace α]
    {K H : Set α} (hK : IsPreconnected K) (hH : IsClosed H) (hHK : H ⊆ K)
    (hb : IsPreconnected (frontier H)) : IsPreconnected (K \ interior H) := by
  rw [isPreconnected_closed_iff]
  intro A B hA hB hcover hCA hCB
  by_contra hn
  have hn' : ∀ x ∈ K \ interior H, ¬ (x ∈ A ∧ x ∈ B) := by
    intro x hx hab
    exact hn ⟨x, hx, hab⟩
  have hbC : frontier H ⊆ K \ interior H := by
    intro x hx
    exact ⟨hHK (hH.closure_eq ▸ hx.1), hx.2⟩
  have hbor : frontier H ⊆ A ∨ frontier H ⊆ B := by
    by_cases ha : frontier H ⊆ A
    · exact Or.inl ha
    · right
      intro x hx
      by_contra hxb
      have hxA : x ∈ A := (hcover (hbC hx)).resolve_right hxb
      obtain ⟨y, hy, hyA⟩ := not_subset.mp ha
      have hyB : y ∈ B := (hcover (hbC hy)).resolve_left hyA
      obtain ⟨z, hz, hzA, hzB⟩ := (isPreconnected_closed_iff.mp hb) A B hA hB
        (hbC.trans hcover) ⟨x, hx, hxA⟩ ⟨y, hy, hyB⟩
      exact hn' z (hbC hz) ⟨hzA, hzB⟩
  wlog hfront : frontier H ⊆ A generalizing A B
  · have hb' : frontier H ⊆ B := hbor.resolve_left hfront
    have hc' : K \ interior H ⊆ B ∪ A := by simpa [union_comm] using hcover
    have hn'' : ¬ ((K \ interior H) ∩ (B ∩ A)).Nonempty := by
      simpa [inter_comm] using hn
    exact this B A hB hA hc' hCB hCA hn''
      (fun x hx h => hn' x hx ⟨h.2, h.1⟩) (Or.inl hb') hb'
  have hkcover : K ⊆ (A ∪ H) ∪ (B ∩ (interior H)ᶜ) := by
    intro x hx
    by_cases hi : x ∈ interior H
    · exact Or.inl (Or.inr (interior_subset hi))
    · rcases hcover ⟨hx, hi⟩ with ha | hb'
      · exact Or.inl (Or.inl ha)
      · exact Or.inr ⟨hb', hi⟩
  obtain ⟨x, hx, hxa⟩ := hCA
  obtain ⟨y, hy, hyb⟩ := hCB
  obtain ⟨z, hzK, hzleft, hzright⟩ := (isPreconnected_closed_iff.mp hK)
    (A ∪ H) (B ∩ (interior H)ᶜ) (hA.union hH)
    (hB.inter isOpen_interior.isClosed_compl) hkcover
    ⟨x, hx.1, Or.inl hxa⟩ ⟨y, hy.1, hyb, hy.2⟩
  have hzC : z ∈ K \ interior H := ⟨hzK, hzright.2⟩
  have hzA : z ∈ A := by
    rcases hzleft with hzA | hzH
    · exact hzA
    · apply hfront
      exact ⟨subset_closure hzH, hzright.2⟩
  exact hn' z hzC ⟨hzA, hzright.1⟩

/-- Removing interiors of finitely many pairwise disjoint closed pieces with
preconnected frontiers preserves preconnectedness. -/
theorem isPreconnected_sdiff_finset_interiors {α ι : Type*} [TopologicalSpace α]
    (K : Set α) (H : ι → Set α) (s : Finset ι) (hK : IsPreconnected K)
    (hclosed : ∀ i, IsClosed (H i)) (hsub : ∀ i, H i ⊆ K)
    (hboundary : ∀ i, IsPreconnected (frontier (H i)))
    (hdisj : ∀ i j, i ≠ j → Disjoint (H i) (H j)) :
    IsPreconnected (K \ ⋃ i ∈ s, interior (H i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hK
  | @insert i s hi ih =>
    rw [Finset.set_biUnion_insert]
    have heq : K \ (interior (H i) ∪ ⋃ j ∈ s, interior (H j)) =
        (K \ ⋃ j ∈ s, interior (H j)) \ interior (H i) := by
      ext x; simp only [mem_sdiff, mem_union]; tauto
    rw [heq]
    apply isPreconnected_sdiff_interior_of_frontier ih (hclosed i) ?_ (hboundary i)
    intro x hx
    refine ⟨hsub i hx, ?_⟩
    intro hxunion
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxunion
    have hij : i ≠ j := by
      intro heq
      subst j
      exact hi hj
    exact disjoint_left.mp (hdisj i j hij) hx (interior_subset hxj)

/-- The core left after removing one parity class of intermediate square
interiors is connected whenever the original compact set is connected. -/
theorem isConnected_dyadic_intermediate_core {N : ℕ} (a : ℂ) (r : ℝ)
    (hr : 0 < r) (j : Fin 4) (K : Set ℂ) (hKc : IsCompact K)
    (hK : IsConnected K)
    (hHK : ∀ i : {i : Fin N × Fin N // squareParity i = j},
      complexIntermediateGridSquare a r i.1 ⊆ K) :
    IsConnected (K \ ⋃ i : {i : Fin N × Fin N // squareParity i = j},
      interior (complexIntermediateGridSquare a r i.1)) := by
  let ι := {i : Fin N × Fin N // squareParity i = j}
  let H : ι → Set ℂ := fun i => complexIntermediateGridSquare a r i.1
  have hp := isPreconnected_sdiff_finset_interiors K H Finset.univ hK.isPreconnected
    (fun i => isClosed_complexIntermediateGridSquare a r i.1) hHK
    (fun i => (isConnected_frontier_complexIntermediateGridSquare a r hr i.1).isPreconnected)
    (by
      intro i k hik
      have hne : i.1 ≠ k.1 := fun h => hik (Subtype.ext h)
      exact (complex_enlarged_grid_squares_disjoint a r hr i.1 k.1
        (i.2.trans k.2.symm) hne).mono
        ((complexIntermediateGridSquare_subset_open_enlarged a r hr i.1).trans
          (complexOpenEnlargedGridSquare_subset a r i.1))
        ((complexIntermediateGridSquare_subset_open_enlarged a r hr k.1).trans
          (complexOpenEnlargedGridSquare_subset a r k.1)))
  have hp' : IsPreconnected (K \ ⋃ i : ι, interior (H i)) := by simpa using hp
  have hnonempty : (K \ ⋃ i : ι, interior (H i)).Nonempty := by
    by_cases hi : Nonempty ι
    · obtain ⟨i⟩ := hi
      obtain ⟨_, _, hat, _⟩ := dyadic_intermediate_compact_core a r hr j K hKc hHK
      obtain ⟨x, _, hx⟩ := hat i
      exact ⟨x, hx⟩
    · let _ : IsEmpty ι := not_nonempty_iff.mp hi
      simpa using hK.nonempty
  exact ⟨hnonempty, hp'⟩

#print axioms isPreconnected_sdiff_interior_of_frontier
#print axioms isPreconnected_sdiff_finset_interiors
#print axioms isConnected_dyadic_intermediate_core
end HarmonicBalls
