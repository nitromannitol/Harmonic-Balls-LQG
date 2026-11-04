import HarmonicBalls.Proofs.Sec10.DirectedContinuumIntersection

/-!
# Separation of proper compact subsets of an irreducible continuum

Minimality between two closed sets forces a relative clopen separation of
those sets in every proper compact subset. This connects the subcontinuum
formulation with the notion of connectedness between sets.
-/

namespace HarmonicBalls

open Set Topology

/-- In a proper compact subset of a continuum irreducible between two closed
sets, the traces of those sets can be separated by a relatively clopen set. -/
theorem irreducible_proper_compact_separates_closed_sets
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {M A B F : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hmin : ∀ N : Set X, N ⊆ M → IsCompact N → IsConnected N →
      (N ∩ A).Nonempty → (N ∩ B).Nonempty → N = M)
    (hFc : IsCompact F) (hFM : F ⊆ M) (hFne : F ≠ M) :
    ∃ V : Set X, IsOpen V ∧ IsClosed (F ∩ V) ∧
      F ∩ A ⊆ V ∧ Disjoint (F ∩ V) B := by
  classical
  let T := F ∩ A
  have hTc : IsCompact T := hFc.inter_right hA
  have hlocal : ∀ x : T, ∃ V : Set X, IsOpen V ∧ x.1 ∈ V ∧
      IsClosed (F ∩ V) ∧ F ∩ V ⊆ Bᶜ := by
    intro x
    have hxF : x.1 ∈ F := x.2.1
    have hxA : x.1 ∈ A := x.2.2
    let C := connectedComponentIn F x.1
    have hCF : C ⊆ F := connectedComponentIn_subset F x.1
    have hxC : x.1 ∈ C := mem_connectedComponentIn hxF
    have hclF : closure C ⊆ F := closure_minimal hCF hFc.isClosed
    have hCc : IsCompact (closure C) := hFc.of_isClosed_subset isClosed_closure hclF
    have hCcon : IsConnected (closure C) := (isConnected_connectedComponentIn_iff.mpr hxF).closure
    have hCB : C ⊆ Bᶜ := by
      intro y hyC hyB
      have heq : closure C = M := hmin _ (hclF.trans hFM) hCc hCcon
        ⟨x.1, subset_closure hxC, hxA⟩ ⟨y, subset_closure hyC, hyB⟩
      have hMF : M ⊆ F := by
        intro z hz
        apply hclF
        rw [heq]
        exact hz
      exact hFne (Subset.antisymm hFM hMF)
    obtain ⟨V, hVo, hCV, hVB, hVcl⟩ :=
      exists_open_inter_compact_component_subset hFc hxF hB.isOpen_compl hCB
    exact ⟨V, hVo, (hCV hxC).2, hVcl, hVB⟩
  choose V hVo hxV hVcl hVB using hlocal
  have hcover : T ⊆ ⋃ x : T, V x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨t, ht⟩ := hTc.elim_finite_subcover V hVo hcover
  let W := ⋃ x ∈ t, V x
  have hWo : IsOpen W := isOpen_biUnion fun x _ => hVo x
  have hWcl : IsClosed (F ∩ W) := by
    have heq : F ∩ W = ⋃ x ∈ t, (F ∩ V x) := by ext z; simp only [W, mem_inter_iff, mem_iUnion]; tauto
    rw [heq]
    exact isClosed_biUnion_finset fun x _ => hVcl x
  refine ⟨W, hWo, hWcl, ht, ?_⟩
  apply Set.disjoint_left.mpr
  intro x hxF hxB
  obtain ⟨y, hy, hxV⟩ := mem_iUnion₂.mp hxF.2
  exact hVB y ⟨hxF.1, hxV⟩ hxB

/-- A closed subset of a compact continuum irreducible between two closed
sets equals the whole continuum if no relative clopen set separates its
traces of the two endpoint sets. -/
theorem irreducible_closed_subset_eq_of_connected_between
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {M A B F : Set X} (hMc : IsCompact M) (hA : IsClosed A) (hB : IsClosed B)
    (hmin : ∀ N : Set X, N ⊆ M → IsCompact N → IsConnected N →
      (N ∩ A).Nonempty → (N ∩ B).Nonempty → N = M)
    (hFclosed : IsClosed F) (hFM : F ⊆ M)
    (hbetween : ∀ V : Set X, IsOpen V → IsClosed (F ∩ V) →
      F ∩ A ⊆ V → ¬ Disjoint (F ∩ V) B) : F = M := by
  by_contra hFne
  have hFc : IsCompact F := hMc.of_isClosed_subset hFclosed hFM
  obtain ⟨V, hVo, hVcl, hAV, hVB⟩ :=
    irreducible_proper_compact_separates_closed_sets hA hB hmin hFc hFM hFne
  exact hbetween V hVo hVcl hAV hVB

end HarmonicBalls
