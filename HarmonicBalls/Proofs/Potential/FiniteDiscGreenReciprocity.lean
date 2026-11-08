import HarmonicBalls.Proofs.Potential.GreenRegularBoundaryGeometry
import HarmonicBalls.Proofs.Sec6.DiscGreenMass
import HarmonicBalls.Proofs.Sec6.GreenDilation
import HarmonicBalls.Proofs.Sec5.LocalCountableDeletion
import HarmonicBalls.Proofs.Sec6.AvoidanceDiscRestart

/-! # Green reciprocity for finite disc families

The component and Green-function infrastructure used here incorporates the
potential-theoretic work of Leonardo Bonanno. This file establishes the
families whose intersecting discs share a containing disc in the family;
general overlaps require a further argument.
-/

namespace HarmonicBalls

open Set Metric Filter
open scoped Topology

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

/-- The harmonic correction has the same pole-shift bound as the
regularized Newtonian kernel, when the regularization discs lie in the domain. -/
theorem greenHarmonicCorrection_pole_shift_le
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {ε : ℝ} (hε : 0 < ε) {z z' y : ℂ} (hy : y ∈ U)
    (hz : closedBall z (2 * ε) ⊆ U) (hz' : closedBall z' (2 * ε) ⊆ U) :
    (greatestHarmonicMinorant U (newtonKernelEReal z') y).toReal -
      (greatestHarmonicMinorant U (newtonKernelEReal z) y).toReal ≤
      (2 * Real.pi)⁻¹ * Real.log (1 + ‖z - z'‖ / ε) := by
  have hzU : z ∈ U := hz (mem_closedBall_self (by positivity))
  have hz'U : z' ∈ U := hz' (mem_closedBall_self (by positivity))
  let H : ℂ → ℂ → ℝ := fun x w =>
    (greatestHarmonicMinorant U (newtonKernelEReal x) w).toReal
  have hreg (x : ℂ) (hx : closedBall x (2 * ε) ⊆ U) (w : ℂ) (hw : w ∈ U) :
      H x w ≤ regularizedNewtonKernel ε x w := by
    have hub : greatestHarmonicMinorant U (newtonKernelEReal x) w ≤
        (regularizedNewtonKernel ε x w : EReal) := by
      rw [greatestHarmonicMinorant_regularized hε hx]
      exact greatestHarmonicMinorant_le hw
    obtain ⟨R, hR⟩ := hUb.subset_closedBall x
    have hlb := (isHarmonicMinorant_const_newtonKernelEReal hR).le_greatestHarmonicMinorant w
    have hb : greatestHarmonicMinorant U (newtonKernelEReal x) w ≠ ⊥ :=
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlb
    exact EReal.toReal_le_toReal hub hb (EReal.coe_ne_top _)
  let C : ℝ := (2 * Real.pi)⁻¹ * Real.log (1 + ‖z - z'‖ / ε)
  let q : ℂ → ℝ := fun w => H z' w - C
  have hq : IsHarmonicMinorant U (newtonKernelEReal z) q := by
    apply (isHarmonicMinorant_regularized_iff hε hz).2
    constructor
    · exact (harmonicOnNhd_greatestHarmonicMinorant_newtonKernel hU hUb hz'U).sub
        (InnerProductSpace.harmonicOnNhd_const C)
    · intro w hw
      change ((H z' w - C : ℝ) : EReal) ≤ (regularizedNewtonKernel ε z w : EReal)
      rw [EReal.coe_le_coe_iff]
      have hshift := regularizedNewtonKernel_sub_le hε z z' w
      have hbound := hreg z' hz' w hw
      dsimp [C] at *
      linarith
  have hlower := hq.le_greatestHarmonicMinorant y
  have hupper : greatestHarmonicMinorant U (newtonKernelEReal z) y ≤
      (regularizedNewtonKernel ε z y : EReal) := by
    rw [greatestHarmonicMinorant_regularized hε hz]
    exact greatestHarmonicMinorant_le hy
  have hreal := EReal.toReal_le_toReal hlower (EReal.coe_ne_bot _)
    (ne_top_of_le_ne_top (EReal.coe_ne_top _) hupper)
  simp only [EReal.toReal_coe] at hreal
  change H z' y - H z y ≤ C
  dsimp [q] at hreal
  linarith

/-- For a fixed observation point in a bounded open set, the harmonic
correction is continuous in the pole. This does not use reciprocity. -/
theorem continuousAt_greenHarmonicCorrection_pole
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z y : ℂ} (hz : z ∈ U) (hy : y ∈ U) :
    ContinuousAt (fun x => (greatestHarmonicMinorant U (newtonKernelEReal x) y).toReal) z := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU z hz
  let ε : ℝ := δ / 8
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hzball : closedBall z (2 * ε) ⊆ U :=
    (closedBall_subset_ball (by dsimp [ε]; linarith)).trans hδU
  have hnear : ∀ x ∈ ball z (δ / 4), closedBall x (2 * ε) ⊆ U := by
    intro x hx w hw
    apply hδU
    rw [mem_ball] at hx ⊢
    rw [mem_closedBall] at hw
    have ht := dist_triangle w x z
    dsimp [ε] at hw
    linarith
  let C : ℂ → ℝ := fun x => (2 * Real.pi)⁻¹ * Real.log (1 + ‖z - x‖ / ε)
  have hC : ContinuousAt C z := by
    dsimp [C]
    fun_prop (disch := simp)
  have hCz : C z = 0 := by simp [C]
  rw [Metric.continuousAt_iff]
  intro η hη
  obtain ⟨κ, hκ, hκC⟩ := Metric.continuousAt_iff.mp hC η hη
  refine ⟨min κ (δ / 4), lt_min hκ (by positivity), ?_⟩
  intro x hx
  have hxball : x ∈ ball z (δ / 4) := mem_ball.mpr (lt_of_lt_of_le hx (min_le_right _ _))
  have hsmall := hκC (lt_of_lt_of_le hx (min_le_left _ _))
  rw [hCz, dist_zero_right] at hsmall
  have h1 := greenHarmonicCorrection_pole_shift_le hU hUb hε hy hzball (hnear x hxball)
  have h2 := greenHarmonicCorrection_pole_shift_le hU hUb hε hy (hnear x hxball) hzball
  rw [norm_sub_rev] at h2
  change _ ≤ C x at h1 h2
  rw [Real.dist_eq]
  have hsmall' : C x < η := lt_of_le_of_lt (le_abs_self (C x)) (by simpa only [Real.norm_eq_abs] using hsmall)
  exact lt_of_le_of_lt (abs_le.mpr ⟨by linarith, h1⟩) hsmall'

/-- The harmonic correction is jointly continuous in the pole and the
observation point throughout a bounded open domain. -/
theorem continuousAt_greenHarmonicCorrection_uncurry
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z y : ℂ} (hz : z ∈ U) (hy : y ∈ U) :
    ContinuousAt (fun p : ℂ × ℂ =>
      (greatestHarmonicMinorant U (newtonKernelEReal p.1) p.2).toReal) (z, y) := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU z hz
  let ε : ℝ := δ / 8
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hzball : closedBall z (2 * ε) ⊆ U :=
    (closedBall_subset_ball (by dsimp [ε]; linarith)).trans hδU
  have hnear : ∀ x ∈ ball z (δ / 4), closedBall x (2 * ε) ⊆ U := by
    intro x hx w hw
    apply hδU
    rw [mem_ball] at hx ⊢
    rw [mem_closedBall] at hw
    have ht := dist_triangle w x z
    dsimp [ε] at hw
    linarith
  let H : ℂ → ℂ → ℝ := fun x w =>
    (greatestHarmonicMinorant U (newtonKernelEReal x) w).toReal
  let C : ℂ → ℝ := fun x => (2 * Real.pi)⁻¹ * Real.log (1 + ‖z - x‖ / ε)
  have hC : ContinuousAt C z := by
    dsimp [C]
    fun_prop (disch := simp)
  have hCz : C z = 0 := by simp [C]
  have hCt : Tendsto (fun p : ℂ × ℂ => C p.1) (𝓝 (z, y)) (𝓝 0) := by
    simpa only [hCz, Function.comp_def] using hC.tendsto.comp (continuous_fst : Continuous (fun p : ℂ × ℂ => p.1)).continuousAt.tendsto
  have hbound : ∀ᶠ p : ℂ × ℂ in 𝓝 (z, y), ‖H p.1 p.2 - H z p.2‖ ≤ C p.1 := by
    have hfirst : ∀ᶠ p : ℂ × ℂ in 𝓝 (z, y), p.1 ∈ ball z (δ / 4) :=
      continuous_fst.continuousAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
    have hsecond : ∀ᶠ p : ℂ × ℂ in 𝓝 (z, y), p.2 ∈ U :=
      continuous_snd.continuousAt (hU.mem_nhds hy)
    filter_upwards [hfirst, hsecond] with p hp hpU
    have h1 := greenHarmonicCorrection_pole_shift_le hU hUb hε hpU hzball (hnear p.1 hp)
    have h2 := greenHarmonicCorrection_pole_shift_le hU hUb hε hpU (hnear p.1 hp) hzball
    rw [norm_sub_rev] at h2
    change H p.1 p.2 - H z p.2 ≤ C p.1 at h1
    change H z p.2 - H p.1 p.2 ≤ C p.1 at h2
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, h1⟩
  have hdiff : Tendsto (fun p : ℂ × ℂ => H p.1 p.2 - H z p.2)
      (𝓝 (z, y)) (𝓝 0) := squeeze_zero_norm' hbound hCt
  have hobs : Tendsto (fun p : ℂ × ℂ => H z p.2)
      (𝓝 (z, y)) (𝓝 (H z y)) :=
    ((harmonicOnNhd_greatestHarmonicMinorant_newtonKernel hU hUb hz y hy).1.continuousAt).tendsto.comp
      continuous_snd.continuousAt
  have hsum := hdiff.add hobs
  change Tendsto (fun p : ℂ × ℂ => H p.1 p.2) (𝓝 (z, y)) (𝓝 (H z y))
  simpa only [zero_add, sub_add_cancel] using hsum

/-- For a fixed observation point, the Green function is continuous in the
pole at interior points away from the diagonal. -/
theorem continuousAt_greenFunction_pole
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z y : ℂ} (hz : z ∈ U) (hy : y ∈ U) (hzy : z ≠ y) :
    ContinuousAt (fun x => greenFunction U x y) z := by
  have hn : ContinuousAt (fun x => newtonKernel x y) z := by
    have h := (harmonicAt_newtonKernel hzy).1.continuousAt
    simpa only [newtonKernel_comm] using h
  have hH := continuousAt_greenHarmonicCorrection_pole hU hUb hz hy
  apply (hn.sub hH).congr
  filter_upwards [hU.mem_nhds hz, isOpen_compl_singleton.mem_nhds hzy] with x hx hxy
  simp only [greenFunction, hx, hy, true_and, mem_compl_iff, mem_singleton_iff] at *
  rw [ite_eq_left hxy]
  rfl

/-- The Green kernel is jointly continuous at interior off-diagonal pairs,
without a reciprocity hypothesis. -/
theorem continuousAt_greenFunction_uncurry
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z y : ℂ} (hz : z ∈ U) (hy : y ∈ U) (hzy : z ≠ y) :
    ContinuousAt (fun p : ℂ × ℂ => greenFunction U p.1 p.2) (z, y) := by
  have hn : ContinuousAt (fun p : ℂ × ℂ => newtonKernel p.1 p.2) (z, y) := by
    unfold newtonKernel
    fun_prop (disch := simp [sub_ne_zero.mpr hzy])
  have hH := continuousAt_greenHarmonicCorrection_uncurry hU hUb hz hy
  apply (hn.sub hH).congr
  have hfst : ∀ᶠ p : ℂ × ℂ in 𝓝 (z, y), p.1 ∈ U :=
    continuous_fst.continuousAt (hU.mem_nhds hz)
  have hsnd : ∀ᶠ p : ℂ × ℂ in 𝓝 (z, y), p.2 ∈ U :=
    continuous_snd.continuousAt (hU.mem_nhds hy)
  have hne : ∀ᶠ p : ℂ × ℂ in 𝓝 (z, y), p.1 ≠ p.2 :=
    isClosed_diagonal.isOpen_compl.mem_nhds hzy
  filter_upwards [hfst, hsnd, hne] with p hp₁ hp₂ hpne
  rw [greenFunction, ite_eq_left ⟨hp₁, hp₂, hpne⟩]
  rfl

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

/-- The normalized angular measure is finite and supported on the closed disc. -/
theorem normalizedCircleMeasure_finite_and_supported (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    MeasureTheory.IsFiniteMeasure (Section6.normalizedCircleMeasure c r) ∧
      Section6.normalizedCircleMeasure c r (closedBall c r)ᶜ = 0 := by
  open MeasureTheory in
  constructor
  · let : IsFiniteMeasure (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
      isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
    let : IsFiniteMeasure (ENNReal.ofReal ((2 * Real.pi)⁻¹) •
        volume.restrict (Ioc (-Real.pi) Real.pi)) :=
      Measure.smul_finite _ ENNReal.ofReal_ne_top
    unfold Section6.normalizedCircleMeasure
    infer_instance
  · rw [Section6.normalizedCircleMeasure, Measure.map_apply (continuous_circleMap c r).measurable
      (isClosed_closedBall.measurableSet.compl)]
    have hempty : circleMap c r ⁻¹' (closedBall c r)ᶜ = ∅ := by
      ext θ
      simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
      exact sphere_subset_closedBall (circleMap_mem_sphere c hr θ)
    rw [hempty, measure_empty]

/-- Integrating a measurable function against normalized angular measure is its
circle average, including the convention for nonintegrable functions. -/
theorem integral_normalizedCircleMeasure_of_measurable (c : ℂ) (r : ℝ) {f : ℂ → ℝ}
    (hf : Measurable f) :
    (∫ z, f z ∂(Section6.normalizedCircleMeasure c r)) = Real.circleAverage f c r := by
  open MeasureTheory in
  rw [Section6.normalizedCircleMeasure, integral_map (continuous_circleMap c r).measurable.aemeasurable
    hf.aestronglyMeasurable, integral_smul_measure]
  rw [Real.circleAverage_eq_integral_add (-Real.pi)]
  have heq := intervalIntegral.integral_comp_add_right
    (f := fun θ => f (circleMap c r θ)) (a := 0) (b := 2 * Real.pi) (-Real.pi)
  rw [heq]
  have hp : 0 + -Real.pi = -Real.pi := by ring
  have hp' : 2 * Real.pi + -Real.pi = Real.pi := by ring
  rw [hp, hp', intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]

/-- Angular measure and the central point mass have the same regularized
Newtonian potential sufficiently far from the closed disc. -/
theorem normalizedCircleMeasure_regularizedNewtonKernel {c w : ℂ} {r ε : ℝ}
    (hr : 0 ≤ r) (hε : 0 < ε)
    (hfar : ∀ x ∈ closedBall c r, ε < ‖x - w‖) :
    (∫ x, regularizedNewtonKernel ε x w ∂(Section6.normalizedCircleMeasure c r)) =
      regularizedNewtonKernel ε c w := by
  have hm : Measurable (fun x => regularizedNewtonKernel ε x w) := by
    exact ((continuous_regularizedNewtonKernel hε).comp (continuous_id.prodMk continuous_const)).measurable
  rw [integral_normalizedCircleMeasure_of_measurable c r hm]
  have hc : c ∈ closedBall c r := mem_closedBall_self hr
  have hw : w ∉ closedBall c r := by
    intro hw
    have := hfar w hw
    simp only [sub_self, norm_zero] at this
    linarith
  have hh : InnerProductSpace.HarmonicOnNhd (newtonKernel w) (closedBall c r) := by
    intro x hx
    exact harmonicAt_newtonKernel (fun h => hw (h ▸ hx))
  have heq : Real.circleAverage (fun x => regularizedNewtonKernel ε x w) c r =
      Real.circleAverage (newtonKernel w) c r := by
    apply Real.circleAverage_congr_sphere
    intro x hx
    change regularizedNewtonKernel ε x w = newtonKernel w x
    rw [regularizedNewtonKernel_of_le_norm (le_of_lt (hfar x (sphere_subset_closedBall (by simpa only [abs_of_nonneg hr] using hx)))),
      newtonKernel_comm]
  have hhavg : Real.circleAverage (newtonKernel w) c r = newtonKernel w c := by
    apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
    simpa only [abs_of_nonneg hr] using hh
  rw [heq, hhavg, regularizedNewtonKernel_of_le_norm (le_of_lt (hfar c hc)),
    newtonKernel_comm]

/-- The harmonic correction satisfies the circle mean-value property in its
pole variable. The thickened closed disc stays inside the open domain. -/
theorem greenHarmonicCorrection_circleAverage_pole
    {U : Set ℂ} (hU : IsOpen U) {c y : ℂ} {r ε : ℝ}
    (hr : 0 ≤ r) (hε : 0 < ε)
    (hthick : cthickening (3 * ε) (closedBall c r) ⊆ U) (hy : y ∈ U) :
    Real.circleAverage (fun x =>
      (greatestHarmonicMinorant U (newtonKernelEReal x) y).toReal) c r =
      (greatestHarmonicMinorant U (newtonKernelEReal c) y).toReal := by
  open MeasureTheory in
  have hf := normalizedCircleMeasure_finite_and_supported c hr
  have hc : c ∈ closedBall c r := mem_closedBall_self hr
  obtain ⟨H, hH, heq, _, havg⟩ := greenHarmonicCorrectionBalayageStep_holds U
    (closedBall c r) (Section6.normalizedCircleMeasure c r) c 1 ε hU
    (isCompact_closedBall c r) hf.1 hf.2 hc hε hthick (by
      intro w hw
      simpa only [one_mul] using normalizedCircleMeasure_regularizedNewtonKernel hr hε hw)
  have hm : Measurable (fun x => H x y) := hH.comp (measurable_id.prodMk measurable_const)
  have ha := havg y hy
  rw [integral_normalizedCircleMeasure_of_measurable c r hm, one_mul] at ha
  calc
    _ = Real.circleAverage (fun x => H x y) c r := by
      apply Real.circleAverage_congr_sphere
      intro x hx
      exact heq x (sphere_subset_closedBall (by simpa only [abs_of_nonneg hr] using hx)) y hy
    _ = H c y := ha
    _ = _ := (heq c hc y hy).symm

/-- Away from the observation point, the Green kernel has the circle
mean-value property in the pole variable. -/
theorem greenFunction_circleAverage_pole
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {c y : ℂ} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε)
    (hthick : cthickening (3 * ε) (closedBall c r) ⊆ U)
    (hy : y ∈ U) (hyout : y ∉ closedBall c r) :
    Real.circleAverage (fun x => greenFunction U x y) c r = greenFunction U c y := by
  have hsub : closedBall c r ⊆ U := (self_subset_cthickening _).trans hthick
  have hc : c ∈ closedBall c r := mem_closedBall_self hr
  have hxy : ∀ x ∈ closedBall c r, x ≠ y := fun x hx h => hyout (h ▸ hx)
  have hh : InnerProductSpace.HarmonicOnNhd (newtonKernel y) (closedBall c r) :=
    fun x hx => harmonicAt_newtonKernel (hxy x hx)
  have hNcont : ContinuousOn (fun x => newtonKernel x y) (sphere c |r|) := by
    intro x hx
    have hx' : x ∈ closedBall c r := sphere_subset_closedBall (by simpa only [abs_of_nonneg hr] using hx)
    have hhx := (harmonicAt_newtonKernel (hxy x hx')).1.continuousAt
    simpa only [newtonKernel_comm] using hhx.continuousWithinAt
  have hHcont : ContinuousOn (fun x => (greatestHarmonicMinorant U (newtonKernelEReal x) y).toReal)
      (sphere c |r|) := by
    intro x hx
    have hx' : x ∈ closedBall c r := sphere_subset_closedBall (by simpa only [abs_of_nonneg hr] using hx)
    exact (continuousAt_greenHarmonicCorrection_pole hU hUb (hsub hx') hy).continuousWithinAt
  have hN : Real.circleAverage (fun x => newtonKernel x y) c r = newtonKernel c y := by
    have he : (fun x => newtonKernel x y) = newtonKernel y := funext (fun x => newtonKernel_comm x y)
    rw [he, newtonKernel_comm c y]
    exact InnerProductSpace.HarmonicOnNhd.circleAverage_eq (by simpa only [abs_of_nonneg hr] using hh)
  have hH := greenHarmonicCorrection_circleAverage_pole hU hr hε hthick hy
  have heq : Real.circleAverage (fun x => greenFunction U x y) c r =
      Real.circleAverage (fun x => newtonKernel x y -
        (greatestHarmonicMinorant U (newtonKernelEReal x) y).toReal) c r := by
    apply Real.circleAverage_congr_sphere
    intro x hx
    have hx' : x ∈ closedBall c r := sphere_subset_closedBall (by simpa only [abs_of_nonneg hr] using hx)
    change greenFunction U x y = _
    rw [greenFunction, ite_eq_left ⟨hsub hx', hy, hxy x hx'⟩]
  have hNi : CircleIntegrable (fun x => newtonKernel x y) c r := by
    apply ContinuousOn.circleIntegrable hr
    simpa only [abs_of_nonneg hr] using hNcont
  have hHi : CircleIntegrable (fun x => (greatestHarmonicMinorant U (newtonKernelEReal x) y).toReal) c r := by
    apply ContinuousOn.circleIntegrable hr
    simpa only [abs_of_nonneg hr] using hHcont
  rw [heq]
  change Real.circleAverage ((fun x => newtonKernel x y) -
    (fun x => (greatestHarmonicMinorant U (newtonKernelEReal x) y).toReal)) c r = _
  rw [Real.circleAverage_sub hNi hHi, hN, hH, greenFunction,
    ite_eq_left ⟨hsub hc, hy, hxy c hc⟩]

#print axioms normalizedCircleMeasure_finite_and_supported
#print axioms integral_normalizedCircleMeasure_of_measurable
#print axioms normalizedCircleMeasure_regularizedNewtonKernel
#print axioms greenHarmonicCorrection_circleAverage_pole
#print axioms greenFunction_circleAverage_pole
#print axioms greenFunction_finite_disc_union_eq_isolated_disc
#print axioms greenFunction_pairwise_disjoint_finite_discs_comm
#print axioms greenFunction_finite_discs_comm_of_intersections_contained
#print axioms greenFunction_laminar_finite_discs_comm
#print axioms greenFunction_disjoint_union_ball_comm_of_mem
#print axioms greenFunction_finite_discs_comm_of_disc_component
#print axioms greenHarmonicCorrection_pole_shift_le
#print axioms continuousAt_greenHarmonicCorrection_pole
#print axioms continuousAt_greenHarmonicCorrection_uncurry
#print axioms continuousAt_greenFunction_pole
#print axioms continuousAt_greenFunction_uncurry
#print axioms greenFunction_countably_punctured_ball_comm
#print axioms greenFunction_neg
#print axioms greenFunction_neg_pair_comm
#print axioms greenFunction_point_reflection
#print axioms greenFunction_point_reflection_pair_comm
#print axioms greenFunction_two_congruent_discs_centres_comm

end HarmonicBalls
