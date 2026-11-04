import HarmonicBalls.Proofs.Sec10.ClosedCrossingContinuum

/-!
# Separating components of compact Hausdorff spaces

Compactness upgrades the description of a component as an intersection of
clopen sets to a single clopen neighborhood inside any given neighborhood.
This is a step towards the boundary-bumping argument for compact continua.
-/

namespace HarmonicBalls

open Set Topology

/-- A component in a compact Hausdorff space has a clopen neighborhood in
any open set containing the component. -/
theorem exists_isClopen_between_connectedComponent_and_open
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (x : X) {U : Set X} (hU : IsOpen U) (hsub : connectedComponent x ⊆ U) :
    ∃ V : Set X, IsClopen V ∧ connectedComponent x ⊆ V ∧ V ⊆ U := by
  classical
  let I := { V : Set X // IsClopen V ∧ x ∈ V }
  have hdisj : Disjoint Uᶜ (⋂ i : I, (i : Set X)) := by
    rw [← connectedComponent_eq_iInter_isClopen x]
    exact disjoint_compl_left_iff_subset.mpr hsub
  obtain ⟨s, hs⟩ := hU.isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun i : I => (i : Set X)) (fun i => i.2.1.isClosed) hdisj
  let V : Set X := ⋂ i ∈ s, (i : Set X)
  have hV : IsClopen V := isClopen_biInter_finset fun i _ => i.2.1
  have hxV : x ∈ V := mem_iInter₂.mpr fun i _ => i.2.2
  have hCV : connectedComponent x ⊆ V := hV.connectedComponent_subset hxV
  have hVU : V ⊆ U := disjoint_compl_left_iff_subset.mp hs
  exact ⟨V, hV, hCV, hVU⟩

/-- For a compact subset of a Hausdorff space, a component contained in an
open set has a relatively clopen neighborhood contained in that open set. -/
theorem exists_open_inter_compact_component_subset
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {F : Set X} (hF : IsCompact F) {x : X} (hx : x ∈ F)
    {U : Set X} (hU : IsOpen U) (hsub : connectedComponentIn F x ⊆ U) :
    ∃ V : Set X, IsOpen V ∧ connectedComponentIn F x ⊆ F ∩ V ∧
      F ∩ V ⊆ U ∧ IsClosed (F ∩ V) := by
  let : CompactSpace F := isCompact_iff_compactSpace.mp hF
  let y : F := ⟨x, hx⟩
  have hsubset : connectedComponent y ⊆ Subtype.val ⁻¹' U := by
    intro z hz
    apply hsub
    rw [connectedComponentIn_eq_image hx]
    exact ⟨z, hz, rfl⟩
  obtain ⟨W, hW, hCW, hWU⟩ :=
    exists_isClopen_between_connectedComponent_and_open y (hU.preimage continuous_subtype_val) hsubset
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.mp hW.isOpen
  have himage : Subtype.val '' W = F ∩ V := by
    rw [← hV, Subtype.image_preimage_coe]
  refine ⟨V, hVo, ?_, ?_, ?_⟩
  · rw [← himage, connectedComponentIn_eq_image hx]
    exact image_mono hCW
  · rw [← himage]
    rintro z ⟨a, ha, rfl⟩
    exact hWU ha
  · rw [← himage]
    exact hF.isClosed.isClosedMap_subtype_val W hW.isClosed

/-- Boundary bumping: in a connected compact Hausdorff space, the closure
of each component of a nonempty proper open set meets its complement. -/
theorem closure_connectedComponentIn_inter_compl_nonempty
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    {O : Set X} (hO : IsOpen O) (hproper : O ≠ univ) {x : X} (hx : x ∈ O) :
    (closure (connectedComponentIn O x) ∩ Oᶜ).Nonempty := by
  classical
  let C := connectedComponentIn O x
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hCO : C ⊆ O := connectedComponentIn_subset O x
  by_contra h
  have hclO : closure C ⊆ O := by
    intro y hy
    by_contra hyO
    exact h ⟨y, hy, hyO⟩
  have hclC : closure C ⊆ C := by
    intro y hy
    have hconn : IsPreconnected (C ∪ {y}) :=
      isPreconnected_connectedComponentIn.subset_closure subset_union_left
        (union_subset subset_closure (singleton_subset_iff.mpr hy))
    have hsub : C ∪ {y} ⊆ O := union_subset hCO (singleton_subset_iff.mpr (hclO hy))
    exact hconn.subset_connectedComponentIn (mem_union_left _ hxC) hsub (mem_union_right _ rfl)
  have hCc : IsClosed C := closure_subset_iff_isClosed.mp hclC
  obtain ⟨U, V, hU, hV, hCU, hOV, hUV⟩ :=
    normal_separation hCc hO.isClosed_compl (disjoint_compl_right.mono_left hCO)
  have hclUO : closure U ⊆ O := by
    have hclUV : closure U ⊆ Vᶜ :=
      closure_minimal (fun z hz hzV => Set.disjoint_left.mp hUV hz hzV) hV.isClosed_compl
    intro z hz
    by_contra hzO
    exact hclUV hz (hOV hzO)
  let F := closure U
  have hFcompact : IsCompact F := isClosed_closure.isCompact
  have hCF : C ⊆ F := hCU.trans subset_closure
  have hxF : x ∈ F := hCF hxC
  have hcomponent : connectedComponentIn F x = C := by
    apply Subset.antisymm
    · exact connectedComponentIn_mono x hclUO
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hxC hCF
  have hcomponentU : connectedComponentIn F x ⊆ U := by rw [hcomponent]; exact hCU
  obtain ⟨W, hWopen, hCW, hWU, hWclosed⟩ :=
    exists_open_inter_compact_component_subset hFcompact hxF hU hcomponentU
  have heq : F ∩ W = U ∩ W := by
    apply Subset.antisymm
    · intro z hz
      exact ⟨hWU hz, hz.2⟩
    · exact inter_subset_inter_left W subset_closure
  have hopen : IsOpen (F ∩ W) := by rw [heq]; exact hU.inter hWopen
  have hclopen : IsClopen (F ∩ W) := ⟨hWclosed, hopen⟩
  have huniv : F ∩ W = univ := hclopen.eq_univ ⟨x, hCW (by rw [hcomponent]; exact hxC)⟩
  have hOuniv : O = univ := univ_subset_iff.mp (by
    rw [← huniv]
    exact hWU.trans (subset_closure.trans hclUO))
  exact hproper hOuniv

end HarmonicBalls
