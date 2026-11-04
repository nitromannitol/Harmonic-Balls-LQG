import HarmonicBalls.Steps.Sec11.ScaledAnnulusBallCover
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Connectivity of finite annular covers

A connected shell forces the intersection graph of its ball cover to be
preconnected. The separation argument is adapted from the open-cover graph
lemma in `SubdiffusiveProcess/CoarseGrainingVocab/Section8Resolvent/
StoppingPartitionIntersectionGraphConnected.lean`.
-/

namespace HarmonicBalls

open Set Metric

/-- An open cover of a preconnected set has a preconnected intersection
graph if each cover member meets the set. -/
theorem SimpleGraph.preconnected_of_open_cover_intersections
    {X I : Type*} [TopologicalSpace X] (K : Set X) (hK : IsPreconnected K)
    (cell : I → Set X) (hopen : ∀ i, IsOpen (cell i))
    (hmeets : ∀ i, (K ∩ cell i).Nonempty) (hcover : K ⊆ ⋃ i, cell i)
    (G : SimpleGraph I)
    (hintersection : ∀ {i j}, i ≠ j → (cell i ∩ cell j).Nonempty → G.Adj i j) :
    G.Preconnected := by
  intro u v
  by_contra huv
  let reachable : Set I := {i | G.Reachable u i}
  let unreachable : Set I := {i | ¬ G.Reachable u i}
  let U : Set X := ⋃ i : reachable, cell i.1
  let V : Set X := ⋃ i : unreachable, cell i.1
  have hUopen : IsOpen U := isOpen_iUnion fun i => hopen i.1
  have hVopen : IsOpen V := isOpen_iUnion fun i => hopen i.1
  have hsub : K ⊆ U ∪ V := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
    by_cases hi : G.Reachable u i
    · exact Or.inl (mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
  have hdisjoint : Disjoint U V := by
    rw [disjoint_left]
    intro x hxU hxV
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxU
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxV
    have hij : i.1 ≠ j.1 := by
      intro h
      exact j.2 (h ▸ i.2)
    exact j.2 (i.2.trans (hintersection hij ⟨x, hxi, hxj⟩).reachable)
  have hU : (K ∩ U).Nonempty := by
    obtain ⟨x, hxK, hxu⟩ := hmeets u
    exact ⟨x, hxK, mem_iUnion.mpr ⟨⟨u, SimpleGraph.Reachable.refl u⟩, hxu⟩⟩
  have hV : (K ∩ V).Nonempty := by
    obtain ⟨x, hxK, hxv⟩ := hmeets v
    exact ⟨x, hxK, mem_iUnion.mpr ⟨⟨v, huv⟩, hxv⟩⟩
  rcases hK.subset_or_subset hUopen hVopen hdisjoint hsub with hKU | hKV
  · obtain ⟨x, hxK, hxV⟩ := hV
    exact disjoint_left.mp hdisjoint (hKU hxK) hxV
  · obtain ⟨x, hxK, hxU⟩ := hU
    exact disjoint_left.mp hdisjoint hxU (hKV hxK)

/-- The intersection graph of balls with centers in a fixed set. -/
def ballIntersectionGraph (centers : Set ℂ) (ε : ℝ) : SimpleGraph centers :=
  SimpleGraph.fromRel fun u v => (ball u.1 ε ∩ ball v.1 ε).Nonempty

/-- If a connected set is covered by positive-radius balls centered in it,
their intersection graph is preconnected. -/
theorem ballIntersectionGraph_preconnected_of_cover
    (K centers : Set ℂ) (ε : ℝ) (hK : IsPreconnected K) (hε : 0 < ε)
    (hcenters : centers ⊆ K) (hcover : K ⊆ ⋃ z ∈ centers, ball z ε) :
    (ballIntersectionGraph centers ε).Preconnected := by
  apply SimpleGraph.preconnected_of_open_cover_intersections K hK
    (fun z : centers => ball z.1 ε) (fun _ => isOpen_ball)
  · intro z
    exact ⟨z.1, hcenters z.2, mem_ball_self hε⟩
  · intro x hx
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, hxz⟩
  · intro i j hij h
    exact ⟨hij, Or.inl h⟩

/-- There is a scale-independent finite family of balls whose unit-scale
intersection graph is preconnected and whose doubled dilations stay inside
the respective corridors. -/
theorem exists_connected_scaled_finite_ball_cover :
    ∃ (ε : ℝ) (centers : Set ℂ), 0 < ε ∧ centers.Finite ∧
      centers ⊆ geometricShell 1 (Real.exp (-1)) 0 ∧
      (ballIntersectionGraph centers ε).Preconnected ∧
      ∀ (s : ℝ) (n : ℕ),
        geometricShell (Real.exp (-s)) (Real.exp (-1)) n ⊆
          ⋃ z ∈ centers, ball (Real.exp (-(s + n)) • z) (Real.exp (-(s + n)) * ε) ∧
        ∀ z ∈ centers, ball (Real.exp (-(s + n)) • z)
          (Real.exp (-(s + n)) * (2 * ε)) ⊆ exponentialAnnulusCorridor s n := by
  obtain ⟨ε, centers, hε, hfinite, hcenters, hcover⟩ := exists_scaled_finite_ball_cover
  refine ⟨ε, centers, hε, hfinite, hcenters, ?_, hcover⟩
  apply ballIntersectionGraph_preconnected_of_cover _ _ _
    isConnected_unit_geometricShell.isPreconnected hε hcenters
  simpa only [Nat.cast_zero, add_zero, neg_zero, Real.exp_zero, one_smul, one_mul] using
    (hcover 0 0).1


/-- In a preconnected graph, one closed walk visits any specified finite set
of vertices. Repeated vertices are allowed. -/
theorem SimpleGraph.exists_closed_walk_visiting_finset
    {I : Type*} (G : SimpleGraph I) (hG : G.Preconnected) (u : I) (t : Finset I) :
    ∃ w : G.Walk u u, ∀ v ∈ t, v ∈ w.support := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    exact ⟨.nil, by simp⟩
  | @insert v t hv ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨p⟩ := hG u v
    refine ⟨w.append (p.append p.reverse), ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (SimpleGraph.Walk.mem_support_append_iff _ _).2
        (Or.inr ((SimpleGraph.Walk.mem_support_append_iff _ _).2 (Or.inl p.end_mem_support)))
    · exact (SimpleGraph.Walk.mem_support_append_iff _ _).2 (Or.inl (hw x hx))

/-- A finite preconnected graph admits a closed walk through every vertex. -/
theorem SimpleGraph.exists_closed_walk_visiting_all
    {I : Type*} [Finite I] (G : SimpleGraph I) (hG : G.Preconnected) (u : I) :
    ∃ w : G.Walk u u, ∀ v, v ∈ w.support := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  obtain ⟨w, hw⟩ := SimpleGraph.exists_closed_walk_visiting_finset G hG u Finset.univ
  exact ⟨w, fun v => hw v (Finset.mem_univ v)⟩

/-- The finite annular ball cover admits one closed walk visiting every ball. -/
theorem exists_scaled_ball_cover_with_visiting_walk :
    ∃ (ε : ℝ) (centers : Set ℂ), 0 < ε ∧ centers.Finite ∧
      centers ⊆ geometricShell 1 (Real.exp (-1)) 0 ∧
      (∃ u : centers, ∃ w : (ballIntersectionGraph centers ε).Walk u u,
        ∀ v : centers, v ∈ w.support) ∧
      ∀ (s : ℝ) (n : ℕ),
        geometricShell (Real.exp (-s)) (Real.exp (-1)) n ⊆
          ⋃ z ∈ centers, ball (Real.exp (-(s + n)) • z) (Real.exp (-(s + n)) * ε) ∧
        ∀ z ∈ centers, ball (Real.exp (-(s + n)) • z)
          (Real.exp (-(s + n)) * (2 * ε)) ⊆ exponentialAnnulusCorridor s n := by
  obtain ⟨ε, centers, hε, hfinite, hcenters, hgraph, hcover⟩ :=
    exists_connected_scaled_finite_ball_cover
  have hunit : geometricShell 1 (Real.exp (-1)) 0 ⊆ ⋃ z ∈ centers, ball z ε := by
    simpa only [Nat.cast_zero, add_zero, neg_zero, Real.exp_zero, one_smul, one_mul] using
      (hcover 0 0).1
  obtain ⟨x, hx⟩ := isConnected_unit_geometricShell.nonempty
  obtain ⟨z, hz, _⟩ := mem_iUnion₂.mp (hunit hx)
  let _ : Finite centers := hfinite.to_subtype
  obtain ⟨w, hw⟩ := SimpleGraph.exists_closed_walk_visiting_all (ballIntersectionGraph centers ε)
    hgraph ⟨z, hz⟩
  exact ⟨ε, centers, hε, hfinite, hcenters, ⟨⟨z, hz⟩, w, hw⟩, hcover⟩


/-- The scaled shell covers may be enumerated as one finite overlapping
chain, with the same number of balls at every scale. -/
theorem exists_scaled_annulus_ball_chain :
    ∃ (ε : ℝ) (N : ℕ) (c : ℕ → ℂ), 0 < ε ∧
      (∀ i, c i ∈ geometricShell 1 (Real.exp (-1)) 0) ∧
      (∀ i < N, (ball (c i) ε ∩ ball (c (i + 1)) ε).Nonempty) ∧
      ∀ (s : ℝ) (n : ℕ),
        geometricShell (Real.exp (-s)) (Real.exp (-1)) n ⊆
          ⋃ i ∈ Finset.range (N + 1),
            ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε) ∧
        ∀ i, ball (Real.exp (-(s + n)) • c i)
          (Real.exp (-(s + n)) * (2 * ε)) ⊆ exponentialAnnulusCorridor s n := by
  classical
  obtain ⟨ε, centers, hε, _, hcenters, ⟨u, w, hvisit⟩, hcover⟩ :=
    exists_scaled_ball_cover_with_visiting_walk
  let c : ℕ → ℂ := fun i => (w.getVert i).1
  refine ⟨ε, w.length, c, hε, ?_, ?_, ?_⟩
  · intro i
    exact hcenters (w.getVert i).2
  · intro i hi
    have hadj := w.adj_getVert_succ hi
    change (w.getVert i ≠ w.getVert (i + 1)) ∧
      ((ball (c i) ε ∩ ball (c (i + 1)) ε).Nonempty ∨
       (ball (c (i + 1)) ε ∩ ball (c i) ε).Nonempty) at hadj
    rcases hadj.2 with h | h
    · exact h
    · simpa only [inter_comm] using h
  · intro s n
    constructor
    · intro x hx
      obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp ((hcover s n).1 hx)
      obtain ⟨i, hi, hiN⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
        (hvisit ⟨z, hz⟩)
      have hci : c i = z := congrArg Subtype.val hi
      apply mem_iUnion₂.mpr
      refine ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
      simpa only [hci] using hxz
    · intro i
      exact (hcover s n).2 (c i) (w.getVert i).2


/-- A fixed sequence of scaled balls and overlap points satisfies the cover,
chain, and corridor hypotheses used in the annular probability estimate. -/
theorem exists_scaled_annulus_cover_chains :
    ∃ (ε : ℝ) (N : ℕ) (c : ℕ → ℂ) (z : ℝ → ℕ → ℕ → ℂ), 0 < ε ∧
      ∀ (s : ℝ) (n : ℕ),
        (∀ i < N,
          z s n (i + 1) ∈ ball (Real.exp (-(s + n)) • c i)
              (Real.exp (-(s + n)) * ε) ∧
          z s n (i + 1) ∈ ball (Real.exp (-(s + n)) • c (i + 1))
              (Real.exp (-(s + n)) * ε)) ∧
        (∀ x ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
          ∃ i ≤ N, x ∈ ball (Real.exp (-(s + n)) • c i)
            (Real.exp (-(s + n)) * ε)) ∧
        (∀ i ≤ N, ball (Real.exp (-(s + n)) • c i)
          (Real.exp (-(s + n)) * (2 * ε)) ⊆ exponentialAnnulusCorridor s n) := by
  classical
  obtain ⟨ε, N, c, hε, _, hover, hcover⟩ := exists_scaled_annulus_ball_chain
  let b : ℕ → ℂ := fun i => if h : i < N then Classical.choose (hover i h) else 0
  have hb : ∀ i < N, b i ∈ ball (c i) ε ∧ b i ∈ ball (c (i + 1)) ε := by
    intro i hi
    simpa only [b, dite_eq_left hi, mem_inter_iff] using Classical.choose_spec (hover i hi)
  let z : ℝ → ℕ → ℕ → ℂ := fun s n j => Real.exp (-(s + n)) • b (j - 1)
  refine ⟨ε, N, c, z, hε, ?_⟩
  intro s n
  let k : ℝ := Real.exp (-(s + n))
  have hk : 0 < k := Real.exp_pos _
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hb' := hb i hi
    constructor <;> rw [← image_real_smul_ball hk]
    · exact ⟨b i, hb'.1, by simp only [z, Nat.add_sub_cancel, k]⟩
    · exact ⟨b i, hb'.2, by simp only [z, Nat.add_sub_cancel, k]⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp ((hcover s n).1 hx)
    exact ⟨i, by have := Finset.mem_range.mp hi; omega, hxi⟩
  · intro i _
    exact (hcover s n).2 i

#print axioms SimpleGraph.preconnected_of_open_cover_intersections
#print axioms exists_scaled_annulus_cover_chains
#print axioms exists_scaled_annulus_ball_chain
#print axioms SimpleGraph.exists_closed_walk_visiting_all
#print axioms exists_scaled_ball_cover_with_visiting_walk
#print axioms ballIntersectionGraph_preconnected_of_cover
#print axioms exists_connected_scaled_finite_ball_cover

end HarmonicBalls
