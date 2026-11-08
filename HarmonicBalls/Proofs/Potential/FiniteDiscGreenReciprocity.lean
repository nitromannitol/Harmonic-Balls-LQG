import HarmonicBalls.Proofs.Potential.GreenRegularBoundaryGeometry
import HarmonicBalls.Proofs.Sec6.DiscGreenMass

/-! # Green reciprocity for finite disc families

The component and Green-function infrastructure used here incorporates the
potential-theoretic work of Leonardo Bonanno. This file establishes the
families whose intersecting discs share a containing disc in the family;
general overlaps require a further argument.
-/

namespace HarmonicBalls

open Set Metric

/-- An isolated disc has the same Green kernel in a finite union as it has
on its own, including observations outside the disc. -/
theorem greenFunction_finite_disc_union_eq_isolated_disc
    {ι : Type*} (F : Finset ι) (c : ι → ℂ) (r : ι → ℝ) {i : ι} (hi : i ∈ F)
    (hdis : ∀ j ∈ F, j ≠ i → Disjoint (ball (c i) (r i)) (ball (c j) (r j)))
    {x : ℂ} (hx : x ∈ ball (c i) (r i)) :
    greenFunction (⋃ j ∈ F, ball (c j) (r j)) x =
      greenFunction (ball (c i) (r i)) x := by
  classical
  let W : Set ℂ := ⋃ j ∈ F.erase i, ball (c j) (r j)
  have hF : (⋃ j ∈ F, ball (c j) (r j)) = ball (c i) (r i) ∪ W := by
    rw [← Finset.insert_erase hi, Finset.set_biUnion_insert]
  have hW : IsOpen W := isOpen_iUnion fun j => isOpen_iUnion fun _ => isOpen_ball
  have hWb : Bornology.IsBounded W :=
    (Bornology.isBounded_biUnion_finset (F.erase i)).2 (fun _ _ => isBounded_ball)
  have hdisW : Disjoint (ball (c i) (r i)) W := by
    apply disjoint_iUnion_right.mpr
    intro j
    apply disjoint_iUnion_right.mpr
    intro hj
    exact hdis j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
  rw [hF]
  exact greenFunction_eq_of_disjoint_open_union_all isOpen_ball hW hdisW
    (isBounded_ball.union hWb) hx

/-- A finite union of pairwise disjoint open discs has a symmetric Green
function, including diagonal and exterior values. -/
theorem greenFunction_pairwise_disjoint_finite_discs_comm
    {ι : Type*} (F : Finset ι) (c : ι → ℂ) (r : ι → ℝ)
    (hdis : ∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      Disjoint (ball (c i) (r i)) (ball (c j) (r j)))
    (x y : ℂ) :
    greenFunction (⋃ i ∈ F, ball (c i) (r i)) x y =
      greenFunction (⋃ i ∈ F, ball (c i) (r i)) y x := by
  by_cases hx : x ∈ ⋃ i ∈ F, ball (c i) (r i)
  · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    have hisol := fun j hj hji => hdis i hi j hj (Ne.symm hji)
    have hxgreen := congrFun (greenFunction_finite_disc_union_eq_isolated_disc F c r hi hisol hxi) y
    by_cases hy : y ∈ ⋃ i ∈ F, ball (c i) (r i)
    · obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hy
      have hygreen := congrFun (greenFunction_finite_disc_union_eq_isolated_disc F c r hj
        (fun k hk hkj => hdis j hj k hk (Ne.symm hkj)) hyj) x
      by_cases hij : i = j
      · subst j
        rw [hxgreen, hygreen, Section6.greenFunction_ball_center_comm]
      · have hyi : y ∉ ball (c i) (r i) :=
          fun h => Set.disjoint_left.mp (hdis i hi j hj hij) h hyj
        have hxj : x ∉ ball (c j) (r j) :=
          fun h => Set.disjoint_left.mp (hdis i hi j hj hij) hxi h
        rw [hxgreen, hygreen, greenFunction_of_notMem_right hyi,
          greenFunction_of_notMem_right hxj]
    · rw [greenFunction_of_notMem_right hy, greenFunction_of_notMem_left hy]
  · rw [greenFunction_of_notMem_left hx, greenFunction_of_notMem_right hx]

/-- Reciprocity holds when every two intersecting discs in a finite family
are contained in one of the family discs. The intersecting discs themselves
need not be nested. -/
theorem greenFunction_finite_discs_comm_of_intersections_contained
    {ι : Type*} (F : Finset ι) (c : ι → ℂ) (r : ι → ℝ)
    (hcover : ∀ i ∈ F, ∀ j ∈ F,
      Disjoint (ball (c i) (r i)) (ball (c j) (r j)) ∨
      ∃ k ∈ F, ball (c i) (r i) ⊆ ball (c k) (r k) ∧
        ball (c j) (r j) ⊆ ball (c k) (r k))
    (x y : ℂ) :
    greenFunction (⋃ i ∈ F, ball (c i) (r i)) x y =
      greenFunction (⋃ i ∈ F, ball (c i) (r i)) y x := by
  classical
  revert hcover
  induction F using Finset.strongInduction with
  | H F ih =>
    intro hcover
    by_cases h : ∃ i ∈ F, ∃ j ∈ F, i ≠ j ∧ ball (c i) (r i) ⊆ ball (c j) (r j)
    · obtain ⟨i, hi, j, hj, hij, hsub⟩ := h
      have hF : (⋃ k ∈ F, ball (c k) (r k)) =
          ⋃ k ∈ F.erase i, ball (c k) (r k) := by
        apply Set.Subset.antisymm
        · intro z hz
          obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.mp hz
          by_cases hki : k = i
          · subst k
            exact mem_iUnion₂.mpr ⟨j, Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩, hsub hzk⟩
          · exact mem_iUnion₂.mpr ⟨k, Finset.mem_erase.mpr ⟨hki, hk⟩, hzk⟩
        · intro z hz
          obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.mp hz
          exact mem_iUnion₂.mpr ⟨k, Finset.mem_of_mem_erase hk, hzk⟩
      rw [hF]
      apply ih (F.erase i) (Finset.erase_ssubset hi)
      intro k hk l hl
      rcases hcover k (Finset.mem_of_mem_erase hk) l (Finset.mem_of_mem_erase hl) with hd | ⟨m, hm, hkm, hlm⟩
      · exact Or.inl hd
      · right
        by_cases hmi : m = i
        · subst m
          exact ⟨j, Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩, hkm.trans hsub, hlm.trans hsub⟩
        · exact ⟨m, Finset.mem_erase.mpr ⟨hmi, hm⟩, hkm, hlm⟩
    · apply greenFunction_pairwise_disjoint_finite_discs_comm F c r
      intro i hi j hj hij
      rcases hcover i hi j hj with hd | ⟨k, hk, hik, hjk⟩
      · exact hd
      · by_cases hki : i = k
        · subst k
          exact False.elim (h ⟨j, hj, i, hi, Ne.symm hij, hjk⟩)
        · exact False.elim (h ⟨i, hi, k, hk, hki, hik⟩)

/-- A finite disc family is covered by the preceding result when its discs
are disjoint or nested. -/
theorem greenFunction_laminar_finite_discs_comm
    {ι : Type*} (F : Finset ι) (c : ι → ℂ) (r : ι → ℝ)
    (hlam : ∀ i ∈ F, ∀ j ∈ F,
      Disjoint (ball (c i) (r i)) (ball (c j) (r j)) ∨
      ball (c i) (r i) ⊆ ball (c j) (r j) ∨
      ball (c j) (r j) ⊆ ball (c i) (r i))
    (x y : ℂ) :
    greenFunction (⋃ i ∈ F, ball (c i) (r i)) x y =
      greenFunction (⋃ i ∈ F, ball (c i) (r i)) y x := by
  apply greenFunction_finite_discs_comm_of_intersections_contained F c r
  intro i hi j hj
  rcases hlam i hi j hj with hd | hs | hs
  · exact Or.inl hd
  · exact Or.inr ⟨j, hj, hs, Subset.rfl⟩
  · exact Or.inr ⟨i, hi, Subset.rfl, hs⟩

#print axioms greenFunction_finite_disc_union_eq_isolated_disc
#print axioms greenFunction_pairwise_disjoint_finite_discs_comm
#print axioms greenFunction_finite_discs_comm_of_intersections_contained
#print axioms greenFunction_laminar_finite_discs_comm

end HarmonicBalls
