import HarmonicBalls.Proofs.Sec10.DirectedContinuumIntersection
import HarmonicBalls.Defs.Geometry

/-!
# Irreducible continua in an annulus

For a continuum irreducible between disjoint closed sets, each one-sided
complement is connected and dense, and their intersection is dense.
-/

namespace HarmonicBalls

open Metric Set Topology

/-- The complement of either endpoint set in an irreducible continuum is
connected and dense. -/
theorem irreducible_compl_connected_dense
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {M A B : Set X} (hMc : IsCompact M) (hM : IsConnected M)
    (hA : IsClosed A) (hAB : Disjoint A B) (hMA : (M ∩ A).Nonempty)
    (hMB : (M ∩ B).Nonempty)
    (hmin : ∀ N : Set X, N ⊆ M → IsCompact N → IsConnected N →
      (N ∩ A).Nonempty → (N ∩ B).Nonempty → N = M) :
    IsConnected (M ∩ Aᶜ) ∧ closure (M ∩ Aᶜ) = M := by
  obtain ⟨b, hbM, hbB⟩ := hMB
  have hbAc : b ∈ Aᶜ := fun hbA => Set.disjoint_left.mp hAB hbA hbB
  let C := connectedComponentIn (M ∩ Aᶜ) b
  have hdense : closure C = M :=
    irreducible_component_compl_dense hMc hM hA hAB hMA hbM hbB hmin
  have hCsub : C ⊆ M ∩ Aᶜ := connectedComponentIn_subset _ b
  have hclsub : M ∩ Aᶜ ⊆ closure C := by rw [hdense]; exact inter_subset_left
  have hpre : IsPreconnected (M ∩ Aᶜ) :=
    isPreconnected_connectedComponentIn.subset_closure hCsub hclsub
  have hconn : IsConnected (M ∩ Aᶜ) := ⟨⟨b, hbM, hbAc⟩, hpre⟩
  have hcl : closure (M ∩ Aᶜ) = M :=
    Subset.antisymm (closure_minimal inter_subset_left hMc.isClosed)
      (calc
        M = closure C := hdense.symm
        _ ⊆ closure (M ∩ Aᶜ) := closure_mono hCsub)
  exact ⟨hconn, hcl⟩

/-- Removing both disjoint closed endpoint sets from an irreducible continuum
leaves a dense subset. -/
theorem irreducible_both_compl_dense
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {M A B : Set X} (hMc : IsCompact M) (hM : IsConnected M)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hMA : (M ∩ A).Nonempty) (hMB : (M ∩ B).Nonempty)
    (hmin : ∀ N : Set X, N ⊆ M → IsCompact N → IsConnected N →
      (N ∩ A).Nonempty → (N ∩ B).Nonempty → N = M) :
    closure (M ∩ Aᶜ ∩ Bᶜ) = M := by
  have hca := (irreducible_compl_connected_dense hMc hM hA hAB hMA hMB hmin).2
  have hmin' : ∀ N : Set X, N ⊆ M → IsCompact N → IsConnected N →
      (N ∩ B).Nonempty → (N ∩ A).Nonempty → N = M :=
    fun N hNM hNc hNcon hNB hNA => hmin N hNM hNc hNcon hNA hNB
  have hcb := (irreducible_compl_connected_dense hMc hM hB hAB.symm hMB hMA hmin').2
  have heq : (M ∩ Bᶜ) ∩ Aᶜ = M ∩ Aᶜ ∩ Bᶜ := by ext x; simp only [mem_inter_iff]; tauto
  have hsub' : M ∩ Aᶜ ⊆ closure (M ∩ Aᶜ ∩ Bᶜ) := by
    have h := hA.isOpen_compl.closure_inter (s := M ∩ Bᶜ)
    rw [hcb, heq] at h
    exact h
  apply Subset.antisymm
  · exact closure_minimal (fun _ hx => hx.1.1) hMc.isClosed
  · calc
      M = closure (M ∩ Aᶜ) := hca.symm
      _ ⊆ closure (M ∩ Aᶜ ∩ Bᶜ) := closure_minimal hsub' isClosed_closure

/-- For an irreducible continuum, a component of the two-sided complement
has closure meeting both endpoint sets exactly when the whole complement is
connected. -/
theorem irreducible_both_compl_connected_iff
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {M A B : Set X} (hMc : IsCompact M) (hM : IsConnected M)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hMA : (M ∩ A).Nonempty) (hMB : (M ∩ B).Nonempty)
    (hmin : ∀ N : Set X, N ⊆ M → IsCompact N → IsConnected N →
      (N ∩ A).Nonempty → (N ∩ B).Nonempty → N = M) :
    IsConnected (M ∩ Aᶜ ∩ Bᶜ) ↔
      ∃ C ∈ connectedComponentsIn (M ∩ Aᶜ ∩ Bᶜ),
        (closure C ∩ A).Nonempty ∧ (closure C ∩ B).Nonempty := by
  let S := M ∩ Aᶜ ∩ Bᶜ
  have hdense : closure S = M := irreducible_both_compl_dense hMc hM hA hB hAB hMA hMB hmin
  constructor
  · intro hS
    obtain ⟨x, hx⟩ := hS.nonempty
    have heq : connectedComponentIn S x = S :=
      Subset.antisymm (connectedComponentIn_subset S x)
        (hS.isPreconnected.subset_connectedComponentIn hx Subset.rfl)
    refine ⟨S, ⟨x, hx, heq⟩, ?_, ?_⟩
    · rw [hdense]
      exact hMA
    · rw [hdense]
      exact hMB
  · rintro ⟨C, ⟨x, hx, rfl⟩, hCA, hCB⟩
    have hCsub : connectedComponentIn S x ⊆ S := connectedComponentIn_subset S x
    have hclsub : closure (connectedComponentIn S x) ⊆ M :=
      closure_minimal (hCsub.trans (fun _ hz => hz.1.1)) hMc.isClosed
    have hCc : IsCompact (closure (connectedComponentIn S x)) :=
      hMc.of_isClosed_subset isClosed_closure hclsub
    have hCcon : IsConnected (closure (connectedComponentIn S x)) :=
      (isConnected_connectedComponentIn_iff.mpr hx).closure
    have hcl : closure (connectedComponentIn S x) = M :=
      hmin _ hclsub hCc hCcon hCA hCB
    have hsub : S ⊆ closure (connectedComponentIn S x) := by
      rw [hcl]
      exact fun _ hz => hz.1.1
    exact ⟨⟨x, hx⟩, isPreconnected_connectedComponentIn.subset_closure hCsub hsub⟩

/-- A compact annular crossing contains an irreducible subcontinuum in the
closed annulus whose open-annulus part is dense. -/
theorem exists_irreducible_closed_annulus_crossing
    {K : Set ℂ} (hKc : IsCompact K) (hK : IsConnected K)
    (w : ℂ) {r R : ℝ} (hrR : r < R)
    (hKball : K ⊆ closedBall w R) (hcross : CrossesAnnulus K w r R) :
    ∃ M : Set ℂ, M ⊆ K ∧ IsCompact M ∧ IsConnected M ∧
      M ⊆ closedBall w R \ ball w r ∧
      (M ∩ sphere w r).Nonempty ∧ (M ∩ sphere w R).Nonempty ∧
      closure (M ∩ annulus w r R) = M := by
  have hAB : Disjoint (sphere w r) (sphere w R) := by
    rw [Set.disjoint_left]
    intro x hx hy
    have hx' := mem_sphere.mp hx
    have hy' := mem_sphere.mp hy
    linarith
  have hKA : (K ∩ sphere w r).Nonempty := by
    simpa [CrossesAnnulus, hKc.isClosed.closure_eq] using hcross.1
  have hKB : (K ∩ sphere w R).Nonempty := by
    simpa [CrossesAnnulus, hKc.isClosed.closure_eq] using hcross.2
  obtain ⟨M, hMK, hMc, hM, hMA, hMB, hmin⟩ :=
    exists_irreducible_subcontinuum_between_closed_sets hKc hK isClosed_sphere
      isClosed_sphere hKA hKB
  have hconn := (irreducible_compl_connected_dense hMc hM isClosed_sphere hAB hMA hMB hmin).1
  have hMout : M ⊆ (ball w r)ᶜ := by
    intro x hxM hxball
    obtain ⟨y, hyM, hyR⟩ := hMB
    have hyA : y ∉ sphere w r := by
      intro hy
      exact Set.disjoint_left.mp hAB hy hyR
    have hcover : M ∩ (sphere w r)ᶜ ⊆ ball w r ∪ (closedBall w r)ᶜ := by
      intro z hz
      by_cases hzr : dist z w < r
      · exact Or.inl (mem_ball.mpr hzr)
      · right
        intro hzclosed
        have hzneq : dist z w ≠ r := fun heq => hz.2 (mem_sphere.mpr heq)
        have hzle := mem_closedBall.mp hzclosed
        exact hzneq (le_antisymm hzle (le_of_not_gt hzr))
    have hxA : x ∉ sphere w r := by
      intro hx
      have hxr := mem_sphere.mp hx
      have hxb := mem_ball.mp hxball
      linarith
    have hyout : y ∈ (closedBall w r)ᶜ := by
      intro hy
      have hyr := mem_sphere.mp hyR
      have hyle := mem_closedBall.mp hy
      linarith
    obtain ⟨z, _, hzball, hzout⟩ := hconn.isPreconnected _ _ isOpen_ball
      isClosed_closedBall.isOpen_compl hcover ⟨x, ⟨hxM, hxA⟩, hxball⟩
      ⟨y, ⟨hyM, hyA⟩, hyout⟩
    exact hzout (ball_subset_closedBall hzball)
  have hMeq : M ∩ annulus w r R = M ∩ (sphere w r)ᶜ ∩ (sphere w R)ᶜ := by
    ext x
    simp only [mem_inter_iff, annulus, mem_sdiff, mem_ball, mem_closedBall,
      mem_compl_iff, mem_sphere]
    constructor
    · rintro ⟨hxM, hxR, hxr⟩
      exact ⟨⟨hxM, by linarith⟩, by linarith⟩
    · rintro ⟨⟨hxM, hxr⟩, hxR⟩
      have hlo : r ≤ dist x w := le_of_not_gt (fun h => hMout hxM (mem_ball.mpr h))
      have hhi : dist x w ≤ R := mem_closedBall.mp (hKball (hMK hxM))
      exact ⟨hxM, lt_of_le_of_ne hhi hxR,
        not_le_of_gt (lt_of_le_of_ne hlo (Ne.symm hxr))⟩
  refine ⟨M, hMK, hMc, hM, ?_, hMA, hMB, ?_⟩
  · exact fun x hx => ⟨hKball (hMK hx), hMout hx⟩
  · rw [hMeq]
    exact irreducible_both_compl_dense hMc hM isClosed_sphere isClosed_sphere
      hAB hMA hMB hmin

end HarmonicBalls
