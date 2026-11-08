import HarmonicBalls.Proofs.Potential.GreenRegularBoundaryGeometry
import HarmonicBalls.Proofs.Sec6.DiscGreenMass
import HarmonicBalls.Proofs.Sec6.GreenDilation
import HarmonicBalls.Proofs.Sec5.LocalCountableDeletion

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

/-- A disc component of a bounded open union has reciprocal Green values
against every point. The other component may have arbitrary geometry. -/
theorem greenFunction_disjoint_union_ball_comm_of_mem
    {c x : ℂ} {r : ℝ} {W : Set ℂ} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) (hdis : Disjoint (ball c r) W)
    (hx : x ∈ ball c r) (y : ℂ) :
    greenFunction (ball c r ∪ W) x y = greenFunction (ball c r ∪ W) y x := by
  have hUb : Bornology.IsBounded (ball c r ∪ W) := isBounded_ball.union hWb
  have hxg := congrFun (greenFunction_eq_of_disjoint_open_union_all
    isOpen_ball hW hdis hUb hx) y
  by_cases hy : y ∈ ball c r
  · have hyg := congrFun (greenFunction_eq_of_disjoint_open_union_all
      isOpen_ball hW hdis hUb hy) x
    rw [hxg, hyg, Section6.greenFunction_ball_center_comm]
  · by_cases hyW : y ∈ W
    · rw [hxg, greenFunction_of_notMem_right hy]
      have hg := greenFunction_eq_zero_of_disjoint_open_components
        hW isOpen_ball hdis.symm (by simpa only [union_comm] using hUb) hyW hx
      simpa only [union_comm] using hg.symm
    · have hyout : y ∉ ball c r ∪ W := by simp [hy, hyW]
      rw [greenFunction_of_notMem_right hyout, greenFunction_of_notMem_left hyout]

/-- A finite disc union is reciprocal at every pair with one point in a
disc containing every disc that meets it. Discs outside this component may
overlap arbitrarily. -/
theorem greenFunction_finite_discs_comm_of_disc_component
    {ι : Type*} (F : Finset ι) (c : ι → ℂ) (r : ι → ℝ) {i : ι} (hi : i ∈ F)
    (hcomponent : ∀ j ∈ F, ball (c j) (r j) ⊆ ball (c i) (r i) ∨
      Disjoint (ball (c i) (r i)) (ball (c j) (r j)))
    {x : ℂ} (hx : x ∈ ball (c i) (r i)) (y : ℂ) :
    greenFunction (⋃ j ∈ F, ball (c j) (r j)) x y =
      greenFunction (⋃ j ∈ F, ball (c j) (r j)) y x := by
  classical
  let G := F.filter (fun j => ¬ ball (c j) (r j) ⊆ ball (c i) (r i))
  let W : Set ℂ := ⋃ j ∈ G, ball (c j) (r j)
  have hF : (⋃ j ∈ F, ball (c j) (r j)) = ball (c i) (r i) ∪ W := by
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hz
      by_cases hs : ball (c j) (r j) ⊆ ball (c i) (r i)
      · exact Or.inl (hs hzj)
      · exact Or.inr (mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hs⟩, hzj⟩)
    · intro z hz
      rcases hz with hz | hz
      · exact mem_iUnion₂.mpr ⟨i, hi, hz⟩
      · obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hz
        exact mem_iUnion₂.mpr ⟨j, (Finset.mem_filter.mp hj).1, hzj⟩
  have hWo : IsOpen W := isOpen_iUnion fun j => isOpen_iUnion fun _ => isOpen_ball
  have hWb : Bornology.IsBounded W :=
    (Bornology.isBounded_biUnion_finset G).2 (fun _ _ => isBounded_ball)
  have hdis : Disjoint (ball (c i) (r i)) W := by
    apply disjoint_iUnion_right.mpr
    intro j
    apply disjoint_iUnion_right.mpr
    intro hj
    obtain ⟨hjF, hjnot⟩ := Finset.mem_filter.mp hj
    exact (hcomponent j hjF).resolve_left hjnot
  rw [hF]
  exact greenFunction_disjoint_union_ball_comm_of_mem hWo hWb hdis hx y

/-- Removing a closed countable set from a disc preserves Green reciprocity,
including at deleted points and on the diagonal. The deleted points may be
irregular boundary points. -/
theorem greenFunction_countably_punctured_ball_comm
    {c : ℂ} {r : ℝ} {K : Set ℂ} (hKc : IsClosed K)
    (hK : (K ∩ ball c r).Countable) (x y : ℂ) :
    greenFunction (ball c r \ K) x y = greenFunction (ball c r \ K) y x := by
  by_cases hx : x ∈ ball c r \ K
  · by_cases hy : y ∈ ball c r \ K
    · by_cases hxy : x = y
      · subst y
        rfl
      · obtain ⟨R, _, hR⟩ := (isBounded_ball : Bornology.IsBounded (ball c r)).subset_ball_lt 0 (0 : ℂ)
        rw [greenFunction_sdiff_of_local_countable isOpen_ball hR hKc hK hx hy (Ne.symm hxy),
          greenFunction_sdiff_of_local_countable isOpen_ball hR hKc hK hy hx hxy,
          Section6.greenFunction_ball_center_comm]
    · rw [greenFunction_of_notMem_right hy, greenFunction_of_notMem_left hy]
  · rw [greenFunction_of_notMem_left hx, greenFunction_of_notMem_right hx]

/-- Simultaneous reflection in the origin preserves the Green kernel of
an arbitrary planar set, including diagonal and exterior values. -/
theorem greenFunction_neg (U : Set ℂ) (x y : ℂ) :
    greenFunction (Neg.neg '' U) (-x) (-y) = greenFunction U x y := by
  have hk : (-1 : ℝ) ≠ 0 := by norm_num
  have hm := Section6.greatestHarmonicMinorant_dilation U (newtonKernelEReal x) hk y
  have hker : (fun z : ℂ => newtonKernelEReal x ((-1 : ℝ)⁻¹ • z)) =
      newtonKernelEReal (-x) := by
    funext z
    simp only [inv_neg, inv_one, neg_one_smul]
    have hNz : newtonKernel x (-z) = newtonKernel (-x) z := by
      unfold newtonKernel
      rw [show -x - z = -(x - -z) by abel, norm_neg]
    have he : -z = x ↔ z = -x := by constructor <;> intro h <;> simpa using congrArg Neg.neg h
    simp only [newtonKernelEReal, he, hNz]
  rw [hker] at hm
  simp only [neg_one_smul] at hm
  have hN : newtonKernel (-x) (-y) = newtonKernel x y := by
    simpa only [newtonKernel, neg_sub_neg] using
      congrArg (fun t : ℝ => -(2 * Real.pi)⁻¹ * Real.log t) (norm_sub_rev y x)
  have hmem (z : ℂ) : -z ∈ Neg.neg '' U ↔ z ∈ U := by
    constructor
    · rintro ⟨w, hw, heq⟩
      have : w = z := neg_injective heq
      simpa only [this] using hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  unfold greenFunction
  rw [hmem x, hmem y]
  simp only [hN, hm]
  split_ifs with h1 h2 <;> try rfl
  · exact False.elim (h2 ⟨h1.1, h1.2.1, fun h => h1.2.2 (congrArg Neg.neg h)⟩)
  · rename_i h2
    exact False.elim (h1 ⟨h2.1, h2.2.1, fun h => h2.2.2 (neg_injective h)⟩)

/-- On a centrally symmetric set, the Green kernel is reciprocal at a pair
of points interchanged by reflection in the origin. -/
theorem greenFunction_neg_pair_comm {U : Set ℂ} (hU : Neg.neg '' U = U) (x : ℂ) :
    greenFunction U x (-x) = greenFunction U (-x) x := by
  have h := greenFunction_neg U x (-x)
  simpa only [hU, neg_neg] using h.symm

/-- The point reflection `z ↦ c - z` preserves the Green kernel when
applied simultaneously to the domain and both arguments. -/
theorem greenFunction_point_reflection (U : Set ℂ) (c x y : ℂ) :
    greenFunction ((fun z : ℂ => c - z) '' U) (c - x) (c - y) =
      greenFunction U x y := by
  have hset : (fun z : ℂ => c - z) '' U = (fun z : ℂ => z + c) '' (Neg.neg '' U) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨-w, ⟨w, hw, rfl⟩, by ring⟩
    · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, by ring⟩
  rw [hset]
  have h := Section6.greenFunction_translate (Neg.neg '' U) c (-x) (-y)
  have h' : greenFunction ((fun z : ℂ => z + c) '' (Neg.neg '' U)) (c - x) (c - y) =
      greenFunction (Neg.neg '' U) (-x) (-y) := by
    simpa only [sub_eq_add_neg, add_comm] using h
  exact h'.trans (greenFunction_neg U x y)

/-- Reciprocity for points exchanged by a central symmetry of the domain. -/
theorem greenFunction_point_reflection_pair_comm {U : Set ℂ} {c : ℂ}
    (hU : (fun z : ℂ => c - z) '' U = U) (x : ℂ) :
    greenFunction U x (c - x) = greenFunction U (c - x) x := by
  have h := greenFunction_point_reflection U c x (c - x)
  simpa only [hU, sub_sub_cancel] using h.symm

/-- The two centres have reciprocal Green values in the union of two
congruent discs, even when their boundaries cross. -/
theorem greenFunction_two_congruent_discs_centres_comm (a : ℂ) (r : ℝ) :
    greenFunction (ball a r ∪ ball (-a) r) a (-a) =
      greenFunction (ball a r ∪ ball (-a) r) (-a) a := by
  have hball (b : ℂ) : Neg.neg '' ball b r = ball (-b) r := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa only [mem_ball, dist_neg_neg] using hw
    · intro hz
      refine ⟨-z, ?_, neg_neg z⟩
      change dist (-z) b < r
      rw [show dist (-z) b = dist z (-b) by simpa only [neg_neg] using dist_neg_neg z (-b)]
      exact hz
  apply greenFunction_neg_pair_comm
  rw [image_union, hball, hball, neg_neg, union_comm]

#print axioms greenFunction_finite_disc_union_eq_isolated_disc
#print axioms greenFunction_pairwise_disjoint_finite_discs_comm
#print axioms greenFunction_finite_discs_comm_of_intersections_contained
#print axioms greenFunction_laminar_finite_discs_comm
#print axioms greenFunction_disjoint_union_ball_comm_of_mem
#print axioms greenFunction_finite_discs_comm_of_disc_component
#print axioms greenFunction_countably_punctured_ball_comm
#print axioms greenFunction_neg
#print axioms greenFunction_neg_pair_comm
#print axioms greenFunction_point_reflection
#print axioms greenFunction_point_reflection_pair_comm
#print axioms greenFunction_two_congruent_discs_centres_comm

end HarmonicBalls
