import HarmonicBalls.Defs.Obstacle
import HarmonicBalls.Proofs.Sec7.ClusterIncrementMass
import Mathlib.Analysis.Normed.Group.Pointwise
import Mathlib.Topology.Order.IntermediateValue

/-!
# A connected cluster cannot cross an empty shell

The topological step in Proposition 7.2: a connected set meeting an earlier
cluster stays inside its thickening if an enclosing shell is empty.
-/

namespace HarmonicBalls

open Metric Set
open scoped Pointwise ENNReal

/-- A connected set meeting `A` and avoiding a surrounding shell is contained
in the inner thickening of `A`. -/
theorem IsPreconnected.subset_thickening_of_disjoint_shell
    {A B : Set ℂ} {r R : ℝ} (hB : IsPreconnected B)
    (hAB : (A ∩ B).Nonempty) (hr : 0 < r) (hrR : r < R)
    (hshell : Disjoint B (thickening R A \ thickening r A)) :
    B ⊆ thickening r A := by
  obtain ⟨a, haA, haB⟩ := hAB
  have hA : A.Nonempty := ⟨a, haA⟩
  intro x hx
  by_contra hxinner
  have hdist : r ≤ infDist x A := by
    rw [mem_thickening_iff_infDist_lt hA] at hxinner
    exact le_of_not_gt hxinner
  have har : infDist a A ≤ r := by rw [infDist_zero_of_mem haA]; exact hr.le
  obtain ⟨y, hyB, hyr⟩ := hB.intermediate_value haB hx
    (continuous_infDist_pt A).continuousOn ⟨har, hdist⟩
  change infDist y A = r at hyr
  have hyouter : y ∈ thickening R A :=
    (mem_thickening_iff_infDist_lt hA).2 (by rw [hyr]; exact hrR)
  have hynot : y ∉ thickening r A := by
    rw [mem_thickening_iff_infDist_lt hA, hyr]
    exact lt_irrefl _
  exact Set.disjoint_left.1 hshell hyB ⟨hyouter, hynot⟩

/-- The same shell barrier gives closure containment in the outer
neighbourhood used in the statement of Proposition 7.2. -/
theorem IsPreconnected.closure_subset_add_ball_of_disjoint_shell
    {A B : Set ℂ} {r R : ℝ} (hB : IsPreconnected B)
    (hAB : (A ∩ B).Nonempty) (hr : 0 < r) (hrR : r < R)
    (hshell : Disjoint B (thickening R A \ thickening r A)) :
    closure B ⊆ A + ball 0 R := by
  rw [add_ball_zero]
  exact (closure_mono (IsPreconnected.subset_thickening_of_disjoint_shell hB hAB hr hrR hshell)).trans
    ((closure_thickening_subset_cthickening r A).trans
      (cthickening_subset_thickening' (lt_trans hr hrR) hrR A))

/-- A cover by Harnack balls excludes a connected increment from the shell.
The hypotheses record the annulus mass lower bound and the Harnack implication
at each member of the cover. -/
theorem closure_subset_add_ball_of_harnack_cover
    {ι : Type*} (μ : MeasureTheory.Measure ℂ) {A B : Set ℂ} {r R : ℝ}
    {ε : ℝ≥0∞} (U V : ι → Set ℂ) (α : ℝ)
    (hB : IsPreconnected B) (hAB : A ⊆ B) (hAne : A.Nonempty)
    (hA : MeasureTheory.NullMeasurableSet A μ) (hAfin : μ A ≠ ⊤)
    (hmass : μ B ≤ μ A + ε) (hr : 0 < r) (hrR : r < R)
    (hcover : thickening R A \ thickening r A ⊆ ⋃ i, V i)
    (hdisjoint : ∀ i, Disjoint (U i) A)
    (hlower : ∀ i, ε ≤ ENNReal.ofReal α * μ (U i))
    (hharnack : ∀ i, μ (B ∩ U i) ≤ ENNReal.ofReal α * μ (U i) → B ∩ V i = ∅) :
    closure B ⊆ A + ball 0 R := by
  apply IsPreconnected.closure_subset_add_ball_of_disjoint_shell hB
    (hAne.mono (fun x hx => ⟨hx, hAB hx⟩)) hr hrR
  apply Set.disjoint_left.2
  intro x hxB hxshell
  obtain ⟨i, hxV⟩ := mem_iUnion.1 (hcover hxshell)
  have hsmall := (measure_inter_le_of_disjoint_of_measure_le_add hAB hA hAfin hmass
    (hdisjoint i)).trans (hlower i)
  have hempty := hharnack i hsmall
  exact (eq_empty_iff_forall_notMem.1 hempty) x ⟨hxB, hxV⟩

/-- A connected set containing its centre cannot escape a ball without
meeting its sphere; a larger ball contains its closure. -/
theorem closure_subset_ball_of_disjoint_sphere
    {B : Set ℂ} {z : ℂ} {r R : ℝ} (hB : IsPreconnected B) (hz : z ∈ B)
    (hr : 0 < r) (hrR : r < R) (hsphere : Disjoint B (sphere z r)) :
    closure B ⊆ ball z R := by
  have hinner : B ⊆ ball z r := by
    intro x hx
    by_contra hxball
    have hdist : r ≤ dist x z := by
      exact le_of_not_gt (by simpa only [mem_ball] using hxball)
    have hzero : dist z z ≤ r := by simpa using hr.le
    obtain ⟨y, hyB, hyr⟩ := hB.intermediate_value hz hx
      (continuous_id.dist continuous_const).continuousOn ⟨hzero, hdist⟩
    change dist y z = r at hyr
    exact Set.disjoint_left.1 hsphere hyB (by simpa only [mem_sphere] using hyr)
  exact (closure_mono hinner).trans
    (closure_ball_subset_closedBall.trans (closedBall_subset_ball hrR))

end HarmonicBalls
