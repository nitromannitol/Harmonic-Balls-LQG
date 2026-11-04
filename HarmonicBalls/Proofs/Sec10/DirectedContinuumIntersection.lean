import HarmonicBalls.Proofs.Sec10.ContinuumBoundaryBumping

/-!
# Intersections of compact continua

A downward directed family of compact connected sets has connected
intersection. This is a step towards constructing irreducible continua.
-/

namespace HarmonicBalls

open Set Topology

/-- A downward directed intersection of nonempty compact connected sets is
connected in a normal Hausdorff space. -/
theorem isConnected_iInter_of_directed_compact
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X] [Nonempty ι]
    (F : ι → Set X) (hcompact : ∀ i, IsCompact (F i))
    (hconnected : ∀ i, IsConnected (F i)) (hdir : Directed (· ⊇ ·) F) :
    IsConnected (⋂ i, F i) := by
  have hclosed (i : ι) : IsClosed (F i) := (hcompact i).isClosed
  have hIclosed : IsClosed (⋂ i, F i) := isClosed_iInter hclosed
  have hIne : (⋂ i, F i).Nonempty :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed F hdir
      (fun i => (hconnected i).nonempty) hcompact hclosed
  refine ⟨hIne, ?_⟩
  intro u v hu hv hcover ⟨x, hxI, hxu⟩ ⟨y, hyI, hyv⟩
  by_contra hnone
  let A := (⋂ i, F i) \ v
  let B := (⋂ i, F i) \ u
  have hAc : IsClosed A := hIclosed.sdiff hv
  have hBc : IsClosed B := hIclosed.sdiff hu
  have hAB : Disjoint A B := by
    rw [disjoint_left]
    intro z hzA hzB
    have hzuv := hcover hzA.1
    rcases hzuv with hzu | hzv
    · exact hzB.2 hzu
    · exact hzA.2 hzv
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := normal_separation hAc hBc hAB
  have hIcover : (⋂ i, F i) ⊆ U ∪ V := by
    intro z hzI
    rcases hcover hzI with hzu | hzv
    · by_cases hzv : z ∈ v
      · exact False.elim (hnone ⟨z, hzI, hzu, hzv⟩)
      · exact Or.inl (hAU ⟨hzI, hzv⟩)
    · by_cases hzu : z ∈ u
      · exact False.elim (hnone ⟨z, hzI, hzu, hzv⟩)
      · exact Or.inr (hBV ⟨hzI, hzu⟩)
  have hxU : x ∈ U := hAU ⟨hxI, fun hxv => hnone ⟨x, hxI, hxu, hxv⟩⟩
  have hyV : y ∈ V := hBV ⟨hyI, fun hyu => hnone ⟨y, hyI, hyu, hyv⟩⟩
  let i₀ : ι := Classical.choice inferInstance
  let S := F i₀ \ (U ∪ V)
  have hSc : IsCompact S := (hcompact i₀).of_isClosed_subset
    ((hclosed i₀).sdiff (hU.union hV)) sdiff_subset
  have hSI : Disjoint S (⋂ i, F i) := by
    rw [disjoint_left]
    intro z hzS hzI
    exact hzS.2 (hIcover hzI)
  obtain ⟨i, hi⟩ := hSc.elim_directed_family_closed F hclosed hSI hdir
  obtain ⟨j, hji, hj0⟩ := hdir i i₀
  have hjcover : F j ⊆ U ∪ V := by
    intro z hzj
    by_contra hzUV
    exact Set.disjoint_left.mp hi ⟨hj0 hzj, hzUV⟩ (hji hzj)
  have hxj : x ∈ F j := mem_iInter.mp hxI j
  have hyj : y ∈ F j := mem_iInter.mp hyI j
  obtain ⟨z, hzj, hzU, hzV⟩ := (hconnected j).isPreconnected U V hU hV hjcover
    ⟨x, hxj, hxU⟩ ⟨y, hyj, hyV⟩
  exact Set.disjoint_left.mp hUV hzU hzV

/-- A compact continuum meeting two closed sets contains a subcontinuum
minimal among those meeting both sets. -/
theorem exists_irreducible_subcontinuum_between_closed_sets
    {X : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]
    {K A B : Set X} (hKc : IsCompact K) (hK : IsConnected K)
    (hA : IsClosed A) (hB : IsClosed B)
    (hKA : (K ∩ A).Nonempty) (hKB : (K ∩ B).Nonempty) :
    ∃ M : Set X, M ⊆ K ∧ IsCompact M ∧ IsConnected M ∧
      (M ∩ A).Nonempty ∧ (M ∩ B).Nonempty ∧
      ∀ N : Set X, N ⊆ M → IsCompact N → IsConnected N →
        (N ∩ A).Nonempty → (N ∩ B).Nonempty → N = M := by
  classical
  let S : Set (Set X) := {N | N ⊆ K ∧ IsCompact N ∧ IsConnected N ∧
    (N ∩ A).Nonempty ∧ (N ∩ B).Nonempty}
  have hKS : K ∈ S := ⟨Subset.rfl, hKc, hK, hKA, hKB⟩
  obtain ⟨M, hMK, hMmin⟩ := zorn_superset_nonempty S (fun c hcS hc hne => by
    let ι := c
    have : Nonempty ι := hne.to_subtype
    let F : ι → Set X := fun i => i.1
    have hFc (i : ι) : IsCompact (F i) := (hcS i.2).2.1
    have hFcon (i : ι) : IsConnected (F i) := (hcS i.2).2.2.1
    have hdir : Directed (· ⊇ ·) F := by
      intro i j
      obtain hij | hji := hc.total i.2 j.2
      · exact ⟨i, Subset.rfl, hij⟩
      · exact ⟨j, hji, Subset.rfl⟩
    let I := ⋂ i, F i
    have hIcon : IsConnected I := isConnected_iInter_of_directed_compact F hFc hFcon hdir
    have hIclosed : IsClosed I := isClosed_iInter fun i => (hFc i).isClosed
    let i₀ : ι := Classical.choice inferInstance
    have hIsub : I ⊆ F i₀ := iInter_subset F i₀
    have hIc : IsCompact I := (hFc i₀).of_isClosed_subset hIclosed hIsub
    have hIK : I ⊆ K := hIsub.trans (hcS i₀.2).1
    have hmeet (D : Set X) (hDc : IsClosed D)
        (hFD : ∀ i, (F i ∩ D).Nonempty) : (I ∩ D).Nonempty := by
      let G : ι → Set X := fun i => F i ∩ D
      have hGc (i : ι) : IsCompact (G i) := (hFc i).inter_right hDc
      have hGdir : Directed (· ⊇ ·) G := by
        intro i j
        obtain ⟨k, hki, hkj⟩ := hdir i j
        exact ⟨k, inter_subset_inter_left D hki, inter_subset_inter_left D hkj⟩
      obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        G hGdir hFD hGc (fun i => (hGc i).isClosed)
      refine ⟨x, mem_iInter.mpr (fun i => (mem_iInter.mp hx i).1), ?_⟩
      exact (mem_iInter.mp hx i₀).2
    have hIA : (I ∩ A).Nonempty := hmeet A hA (fun i => (hcS i.2).2.2.2.1)
    have hIB : (I ∩ B).Nonempty := hmeet B hB (fun i => (hcS i.2).2.2.2.2)
    refine ⟨I, ⟨hIK, hIc, hIcon, hIA, hIB⟩, ?_⟩
    intro N hNc
    exact iInter_subset F ⟨N, hNc⟩) K hKS
  refine ⟨M, hMmin.prop.1, hMmin.prop.2.1, hMmin.prop.2.2.1,
    hMmin.prop.2.2.2.1, hMmin.prop.2.2.2.2, ?_⟩
  intro N hNM hNc hNcon hNA hNB
  exact (hMmin.eq_of_ge ⟨hNM.trans hMmin.prop.1, hNc, hNcon, hNA, hNB⟩ hNM).symm

/-- If a continuum is irreducible between disjoint closed sets, the component
of the complement of either set containing a point of the other is dense. -/
theorem irreducible_component_compl_dense
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {M A B : Set X} (hMc : IsCompact M) (hM : IsConnected M)
    (hA : IsClosed A) (hAB : Disjoint A B) (hMA : (M ∩ A).Nonempty)
    {b : X} (hbM : b ∈ M) (hbB : b ∈ B)
    (hmin : ∀ N : Set X, N ⊆ M → IsCompact N → IsConnected N →
      (N ∩ A).Nonempty → (N ∩ B).Nonempty → N = M) :
    closure (connectedComponentIn (M ∩ Aᶜ) b) = M := by
  have hbAc : b ∈ Aᶜ := fun hbA => Set.disjoint_left.mp hAB hbA hbB
  let C := connectedComponentIn (M ∩ Aᶜ) b
  have hbC : b ∈ C := mem_connectedComponentIn ⟨hbM, hbAc⟩
  have hCsub : C ⊆ M := (connectedComponentIn_subset _ b).trans inter_subset_left
  have hclsub : closure C ⊆ M := closure_minimal hCsub hMc.isClosed
  have hclcompact : IsCompact (closure C) := hMc.of_isClosed_subset isClosed_closure hclsub
  have hCconnected : IsConnected C :=
    isConnected_connectedComponentIn_iff.mpr (show b ∈ M ∩ Aᶜ from ⟨hbM, hbAc⟩)
  have hclconnected : IsConnected (closure C) := hCconnected.closure
  have hout : (M \ Aᶜ).Nonempty := by
    obtain ⟨a, haM, haA⟩ := hMA
    exact ⟨a, haM, by simpa only [mem_compl_iff, not_not] using haA⟩
  obtain ⟨a, haCl, _, haA⟩ :=
    IsConnected.closure_component_inter_open_meets_compl hM hMc hA.isOpen_compl hout ⟨hbM, hbAc⟩
  have hclA : (closure C ∩ A).Nonempty :=
    ⟨a, haCl, by simpa only [mem_compl_iff, not_not] using haA⟩
  have hclB : (closure C ∩ B).Nonempty := ⟨b, subset_closure hbC, hbB⟩
  exact hmin (closure C) hclsub hclcompact hclconnected hclA hclB

end HarmonicBalls
