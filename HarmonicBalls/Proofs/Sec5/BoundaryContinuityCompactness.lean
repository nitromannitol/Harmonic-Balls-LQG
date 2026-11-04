import HarmonicBalls.Steps.Sec5.ContinuityAssembly
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Compactness reduction for right continuity

For an increasing family inside a fixed compact set, right continuity in the
one-sided Hausdorff sense is equivalent to the absence of new points in the
intersection of the closures at decreasing times. This is a deterministic
reduction; identifying that intersection for LQG clusters remains separate.
-/

namespace HarmonicBalls

open Metric Set
open scoped Pointwise

/-- A decreasing dyadic family of closed future sets yields uniform containment
in any open set containing its intersection, by compactness. -/
theorem eventually_closure_subset_open_of_iInter_subset
    {F : ℝ → Set ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s')
    (hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1)
    {U : Set ℂ} (hU : IsOpen U)
    (hinter : (⋂ n : ℕ, closure (F (t + (2 : ℝ)⁻¹ ^ n))) ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ), closure (F s) ⊆ U := by
  let K : ℕ → Set ℂ := fun n => closure (F (t + (2 : ℝ)⁻¹ ^ n))
  have hanti : Antitone K := by
    intro i j hij
    apply closure_mono
    apply hmono
    · positivity
    · exact add_le_add le_rfl (pow_le_pow_of_le_one (show (0 : ℝ) ≤ (2 : ℝ)⁻¹ by norm_num) (show (2 : ℝ)⁻¹ ≤ 1 by norm_num) hij)
  have hc : IsCompact (closedBall (0 : ℂ) 1 \ U) :=
    (show IsCompact (closedBall (0 : ℂ) 1) from isCompact_closedBall (0 : ℂ) 1).diff hU
  have hd : Disjoint (closedBall (0 : ℂ) 1 \ U) (⋂ n, K n) := by
    apply Set.disjoint_left.mpr
    intro x hx hxK
    exact hx.2 (hinter hxK)
  obtain ⟨n, hn⟩ := hc.elim_directed_family_closed K (fun _ => isClosed_closure) hd
    hanti.directed_ge
  refine ⟨(2 : ℝ)⁻¹ ^ n, by positivity, ?_⟩
  intro s hs x hx
  have hxs : x ∈ K n := closure_mono (hmono s _ (lt_of_lt_of_le ht hs.1) hs.2) hx
  have hxb : x ∈ closedBall (0 : ℂ) 1 := by
    exact (closure_mono (hbound s (lt_of_lt_of_le ht hs.1)) hx) |> 
      isClosed_closedBall.closure_subset_iff.mpr ball_subset_closedBall
  by_contra hxU
  exact Set.disjoint_left.mp hn ⟨hxb, hxU⟩ hxs

/-- For bounded increasing sets, one-sided Hausdorff right continuity is
exactly the absence of new points in the intersection of closed future sets. -/
theorem closure_dyadic_iInter_subset_iff_right_continuous
    {F : ℝ → Set ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s')
    (hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1) :
    (⋂ n : ℕ, closure (F (t + (2 : ℝ)⁻¹ ^ n))) ⊆ closure (F t) ↔
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (F s) ⊆ F t + ball (0 : ℂ) ε := by
  constructor
  · intro hinter ε hε
    have h := eventually_closure_subset_open_of_iInter_subset ht hmono hbound
      (U := thickening ε (F t)) isOpen_thickening
      (hinter.trans (closure_subset_thickening hε (F t)))
    obtain ⟨δ, hδ, hδ'⟩ := h
    refine ⟨δ, hδ, fun s hs x hx => ?_⟩
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp (hδ' s hs hx)
    refine ⟨y, hy, x - y, ?_, by abel⟩
    simpa [mem_ball, dist_eq_norm] using hxy
  · intro h x hx
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2 : ℝ)⁻¹ < 1)
    have hx' : x ∈ F t + ball (0 : ℂ) ε := hδ' _ ⟨le_add_of_nonneg_right (by positivity), by linarith⟩
      (Set.mem_iInter.mp hx n)
    obtain ⟨y, hy, z, hz, rfl⟩ := hx'
    refine ⟨y, hy, ?_⟩
    simpa [mem_ball, dist_eq_norm] using hz

/-- For a fixed measure and centre, the cluster-specific issue in right
continuity is the identification of the closed intersection at dyadic times. -/
theorem cluster_closure_dyadic_iInter_subset_iff_right_continuous
    {μ : MeasureTheory.Measure ℂ} {z : ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → cluster μ 1 z s ⊆ cluster μ 1 z s') :
    (⋂ n : ℕ, closure (cluster μ 1 z (t + (2 : ℝ)⁻¹ ^ n))) ⊆
        closure (cluster μ 1 z t) ↔
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (cluster μ 1 z s) ⊆ cluster μ 1 z t + ball (0 : ℂ) ε :=
  closure_dyadic_iInter_subset_iff_right_continuous ht hmono
    (fun _ _ => cluster_subset_ball)

/-- The closed cluster at time `t` is always contained in every later
closed cluster, so right continuity is equivalent to equality. -/
theorem cluster_closure_dyadic_iInter_eq_iff_right_continuous
    {μ : MeasureTheory.Measure ℂ} {z : ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → cluster μ 1 z s ⊆ cluster μ 1 z s') :
    (⋂ n : ℕ, closure (cluster μ 1 z (t + (2 : ℝ)⁻¹ ^ n))) =
        closure (cluster μ 1 z t) ↔
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (cluster μ 1 z s) ⊆ cluster μ 1 z t + ball (0 : ℂ) ε := by
  rw [← cluster_closure_dyadic_iInter_subset_iff_right_continuous ht hmono]
  constructor
  · exact fun h => h.subset
  · intro h
    apply Set.Subset.antisymm h
    intro x hx
    apply Set.mem_iInter.mpr
    intro n
    exact closure_mono (hmono t _ ht (le_add_of_nonneg_right (by positivity))) hx

end HarmonicBalls
