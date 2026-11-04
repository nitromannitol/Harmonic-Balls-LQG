import HarmonicBalls.Proofs.Sec10.LocalizedFrontierPaths

/-! # Paths and components in the planar separation statement

The singleton-intersection specialization of Janiszewski's theorem may be
formulated either with paths or with connected components. This file proves
only the equivalence of the formulations; it does not assert either one.
-/

namespace HarmonicBalls

open Set

/-- In an open subset of a locally path-connected space, two points are in the
same connected component precisely when they can be joined inside the set. -/
theorem mem_connectedComponentIn_iff_joinedIn_of_isOpen
    {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
    {S : Set X} (hS : IsOpen S) {x y : X} :
    y ∈ connectedComponentIn S x ↔ JoinedIn S x y := by
  constructor
  · intro hy
    have hx : x ∈ S := by
      by_contra hn
      have hempty : connectedComponentIn S x = ∅ := by
        rw [connectedComponentIn]
        simp only [hn, ↓reduceDIte]
      rw [hempty] at hy
      exact notMem_empty y hy
    have hc : IsConnected (connectedComponentIn S x) :=
      isConnected_connectedComponentIn_iff.mpr hx
    exact ((hS.connectedComponentIn.isConnected_iff_isPathConnected.mp hc).joinedIn
      x (mem_connectedComponentIn hx) y hy).mono (connectedComponentIn_subset _ _)
  · rintro ⟨p, hp⟩
    have hxs : x ∈ range p := ⟨0, p.source⟩
    have hys : y ∈ range p := ⟨1, p.target⟩
    have hsub : range p ⊆ S := by
      rintro z ⟨t, rfl⟩
      exact hp t
    exact (isConnected_range p.continuous).isPreconnected.subset_connectedComponentIn
      hxs hsub hys

/-- The singleton-intersection separation principle stated using paths
between distinct points is equivalent to its connected-component formulation.
This equivalence does not prove the separation principle. -/
theorem singleton_separation_path_iff_component :
    (∀ (A B : Set ℂ) (a x y : ℂ), IsCompact A → IsCompact B →
      A ∩ B = {a} → x ≠ y → JoinedIn Aᶜ x y → JoinedIn Bᶜ x y →
      JoinedIn (A ∪ B)ᶜ x y) ↔
    (∀ (A B : Set ℂ) (a x y : ℂ), IsCompact A → IsCompact B →
      A ∩ B = {a} → y ∈ connectedComponentIn Aᶜ x →
      y ∈ connectedComponentIn Bᶜ x → y ∈ connectedComponentIn (A ∪ B)ᶜ x) := by
  constructor
  · intro h A B a x y hA hB hab hAx hBx
    have hpathA := (mem_connectedComponentIn_iff_joinedIn_of_isOpen hA.isClosed.isOpen_compl).mp hAx
    have hpathB := (mem_connectedComponentIn_iff_joinedIn_of_isOpen hB.isClosed.isOpen_compl).mp hBx
    apply (mem_connectedComponentIn_iff_joinedIn_of_isOpen (hA.union hB).isClosed.isOpen_compl).mpr
    by_cases hxy : x = y
    · subst y
      apply JoinedIn.refl
      rintro (hxA | hxB)
      · exact hpathA.source_mem hxA
      · exact hpathB.source_mem hxB
    · exact h A B a x y hA hB hab hxy hpathA hpathB
  · intro h A B a x y hA hB hab _ hpathA hpathB
    apply (mem_connectedComponentIn_iff_joinedIn_of_isOpen (hA.union hB).isClosed.isOpen_compl).mp
    exact h A B a x y hA hB hab
      ((mem_connectedComponentIn_iff_joinedIn_of_isOpen hA.isClosed.isOpen_compl).mpr hpathA)
      ((mem_connectedComponentIn_iff_joinedIn_of_isOpen hB.isClosed.isOpen_compl).mpr hpathB)

end HarmonicBalls
