import HarmonicBalls.Proofs.Sec10.IrreducibleCompactSeparation
import HarmonicBalls.Proofs.Sec10.DenseAnnularCrossing

/-!
# The two-sided complement of an irreducible continuum

Removing disjoint closed endpoint sets from a compact continuum irreducible
between them leaves a connected dense set.
-/

namespace HarmonicBalls

open Set Topology

/-- Removing two disjoint closed endpoint sets from a compact continuum
irreducible between them leaves a connected set. -/
theorem irreducible_both_compl_connected
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {M A B : Set X} (hMc : IsCompact M) (hM : IsConnected M)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hMA : (M ∩ A).Nonempty) (hMB : (M ∩ B).Nonempty)
    (hmin : ∀ N : Set X, N ⊆ M → IsCompact N → IsConnected N →
      (N ∩ A).Nonempty → (N ∩ B).Nonempty → N = M) :
    IsConnected (M ∩ Aᶜ ∩ Bᶜ) := by
  classical
  let S := M ∩ Aᶜ ∩ Bᶜ
  have hdense : closure S = M := irreducible_both_compl_dense hMc hM hA hB hAB hMA hMB hmin
  have hSnon : S.Nonempty := by
    by_contra h
    have hempty : S = ∅ := not_nonempty_iff_eq_empty.mp h
    rw [hempty, closure_empty] at hdense
    exact hM.nonempty.ne_empty hdense.symm
  refine ⟨hSnon, ?_⟩
  intro U V hU hV hcover ⟨x, hxS, hxU⟩ ⟨y, hyS, hyV⟩
  by_contra hno
  have hdisj : ∀ z ∈ S, ¬ (z ∈ U ∧ z ∈ V) := by
    intro z hz ⟨hzU, hzV⟩
    exact hno ⟨z, hz, hzU, hzV⟩
  let U₀ := Aᶜ ∩ Bᶜ ∩ U
  let V₀ := Aᶜ ∩ Bᶜ ∩ V
  have hU₀ : IsOpen U₀ := (hA.isOpen_compl.inter hB.isOpen_compl).inter hU
  have hV₀ : IsOpen V₀ := (hA.isOpen_compl.inter hB.isOpen_compl).inter hV
  let F := M ∩ U₀ᶜ
  let G := M ∩ V₀ᶜ
  have hFclosed : IsClosed F := hMc.isClosed.inter hU₀.isClosed_compl
  have hGclosed : IsClosed G := hMc.isClosed.inter hV₀.isClosed_compl
  have hFc : IsCompact F := hMc.of_isClosed_subset hFclosed inter_subset_left
  have hGc : IsCompact G := hMc.of_isClosed_subset hGclosed inter_subset_left
  have hFne : F ≠ M := by
    intro heq
    have hxF : x ∈ F := heq.symm ▸ hxS.1.1
    exact hxF.2 ⟨⟨hxS.1.2, hxS.2⟩, hxU⟩
  have hGne : G ≠ M := by
    intro heq
    have hyG : y ∈ G := heq.symm ▸ hyS.1.1
    exact hyG.2 ⟨⟨hyS.1.2, hyS.2⟩, hyV⟩
  obtain ⟨W, hWo, hFWclosed, hFA, hFB⟩ :=
    irreducible_proper_compact_separates_closed_sets hA hB hmin hFc inter_subset_left hFne
  obtain ⟨Z, hZo, hGZclosed, hGA, hGB⟩ :=
    irreducible_proper_compact_separates_closed_sets hA hB hmin hGc inter_subset_left hGne
  let P := F ∩ W
  let Q := F ∩ Wᶜ
  let P' := G ∩ Z
  let Q' := G ∩ Zᶜ
  have hQclosed : IsClosed Q := hFclosed.inter hWo.isClosed_compl
  have hQ'closed : IsClosed Q' := hGclosed.inter hZo.isClosed_compl
  have hFG : M ⊆ F ∪ G := by
    intro z hzM
    by_contra hz
    have hzF : z ∉ F := fun h => hz (Or.inl h)
    have hzG : z ∉ G := fun h => hz (Or.inr h)
    have hzU₀ : z ∈ U₀ := by
      by_contra hn
      exact hzF ⟨hzM, hn⟩
    have hzV₀ : z ∈ V₀ := by
      by_contra hn
      exact hzG ⟨hzM, hn⟩
    have hzS : z ∈ S := ⟨⟨hzM, hzU₀.1.1⟩, hzU₀.1.2⟩
    exact hdisj z hzS ⟨hzU₀.2, hzV₀.2⟩
  have hFGends : F ∩ G ⊆ A ∪ B := by
    intro z ⟨hzF, hzG⟩
    by_contra hz
    have hzA : z ∉ A := fun h => hz (Or.inl h)
    have hzB : z ∉ B := fun h => hz (Or.inr h)
    have hzS : z ∈ S := ⟨⟨hzF.1, hzA⟩, hzB⟩
    rcases hcover hzS with hzU | hzV
    · exact hzF.2 ⟨⟨hzA, hzB⟩, hzU⟩
    · exact hzG.2 ⟨⟨hzA, hzB⟩, hzV⟩
  have hsame : ∀ z ∈ F, z ∈ G → (z ∈ W ↔ z ∈ Z) := by
    intro z hzF hzG
    rcases hFGends ⟨hzF, hzG⟩ with hzA | hzB
    · have hzW : z ∈ W := hFA ⟨hzF, hzA⟩
      have hzZ : z ∈ Z := hGA ⟨hzG, hzA⟩
      exact ⟨fun _ => hzZ, fun _ => hzW⟩
    · have hzW : z ∉ W := fun hz => Set.disjoint_left.mp hFB ⟨hzF, hz⟩ hzB
      have hzZ : z ∉ Z := fun hz => Set.disjoint_left.mp hGB ⟨hzG, hz⟩ hzB
      exact ⟨fun hz => (hzW hz).elim, fun hz => (hzZ hz).elim⟩
  have hcov : M ⊆ (P ∪ P') ∪ (Q ∪ Q') := by
    intro z hz
    rcases hFG hz with hzF | hzG
    · by_cases hzW : z ∈ W
      · exact Or.inl (Or.inl ⟨hzF, hzW⟩)
      · exact Or.inr (Or.inl ⟨hzF, hzW⟩)
    · by_cases hzZ : z ∈ Z
      · exact Or.inl (Or.inr ⟨hzG, hzZ⟩)
      · exact Or.inr (Or.inr ⟨hzG, hzZ⟩)
  have hsep : Disjoint (P ∪ P') (Q ∪ Q') := by
    apply Set.disjoint_left.mpr
    intro z hzL hzR
    rcases hzL with hzP | hzP' <;> rcases hzR with hzQ | hzQ'
    · exact hzQ.2 hzP.2
    · exact hzQ'.2 ((hsame z hzP.1 hzQ'.1).mp hzP.2)
    · exact hzQ.2 ((hsame z hzQ.1 hzP'.1).mpr hzP'.2)
    · exact hzQ'.2 hzP'.2
  have hleft : (M ∩ (P ∪ P')).Nonempty := by
    obtain ⟨a, haM, haA⟩ := hMA
    have haF : a ∈ F := ⟨haM, fun ha => ha.1.1 haA⟩
    exact ⟨a, haM, Or.inl ⟨haF, hFA ⟨haF, haA⟩⟩⟩
  have hright : (M ∩ (Q ∪ Q')).Nonempty := by
    obtain ⟨b, hbM, hbB⟩ := hMB
    have hbF : b ∈ F := ⟨hbM, fun hb => hb.1.2 hbB⟩
    have hbW : b ∉ W := fun hb => Set.disjoint_left.mp hFB ⟨hbF, hb⟩ hbB
    exact ⟨b, hbM, Or.inl ⟨hbF, hbW⟩⟩
  obtain ⟨z, _, hzL, hzR⟩ := isPreconnected_closed_iff.mp hM.isPreconnected
    (P ∪ P') (Q ∪ Q') (hFWclosed.union hGZclosed) (hQclosed.union hQ'closed)
    hcov hleft hright
  exact Set.disjoint_left.mp hsep hzL hzR

/-- A compact continuum crossing two circles has a component of its open
annular intersection which crosses both circles. -/
theorem IsConnected.exists_annular_component_crossing
    {K : Set ℂ} (hK : IsConnected K) (hKc : IsCompact K)
    (w : ℂ) {r R : ℝ} (hrR : r < R)
    (hKball : K ⊆ Metric.closedBall w R) (hcross : CrossesAnnulus K w r R) :
    (crossingComponents (K ∩ annulus w r R) w r R).Nonempty := by
  obtain ⟨M, hMK, hMc, hM, hMann, hMA, hMB, hdense, hmin⟩ :=
    exists_minimal_closed_annulus_crossing hKc hK w hrR hKball hcross
  have hAB : Disjoint (Metric.sphere w r) (Metric.sphere w R) := by
    rw [Set.disjoint_left]
    intro x hx hy
    have hx' := Metric.mem_sphere.mp hx
    have hy' := Metric.mem_sphere.mp hy
    linarith
  have heq : M ∩ annulus w r R = M ∩ (Metric.sphere w r)ᶜ ∩ (Metric.sphere w R)ᶜ := by
    ext x
    simp only [mem_inter_iff, annulus, mem_sdiff, Metric.mem_ball, Metric.mem_closedBall,
      mem_compl_iff, Metric.mem_sphere]
    constructor
    · rintro ⟨hxM, hxR, hxr⟩
      exact ⟨⟨hxM, by linarith⟩, by linarith⟩
    · rintro ⟨⟨hxM, hxr⟩, hxR⟩
      have hx := hMann hxM
      have hlo : r ≤ dist x w := le_of_not_gt (fun h => hx.2 (Metric.mem_ball.mpr h))
      have hhi : dist x w ≤ R := Metric.mem_closedBall.mp hx.1
      exact ⟨hxM, lt_of_le_of_ne hhi hxR,
        not_le_of_gt (lt_of_le_of_ne hlo (Ne.symm hxr))⟩
  have hS : IsConnected (M ∩ annulus w r R) := by
    rw [heq]
    exact irreducible_both_compl_connected hMc hM Metric.isClosed_sphere Metric.isClosed_sphere
      hAB hMA hMB hmin
  have hSK : M ∩ annulus w r R ⊆ K ∩ annulus w r R :=
    inter_subset_inter_left _ hMK
  have hMcl : M ⊆ closure (M ∩ annulus w r R) := hdense.symm.subset
  obtain ⟨D, hD, _⟩ := dense_annular_crossing_subset_component w r R hSK hS hMcl hMA hMB
  exact ⟨D, hD⟩

end HarmonicBalls
