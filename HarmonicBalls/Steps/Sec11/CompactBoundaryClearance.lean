import HarmonicBalls.Steps.Sec11.BoundaryClearanceStability
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! # Uniform boundary clearance for compact subsets -/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

private structure ClearancePoint where
  val : ℂ

/-- A compact subset of an open set has a positive uniform distance to the
complement in any metric inducing the Euclidean topology. -/
theorem IsEuclideanLengthMetric.exists_uniform_boundary_clearance
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∀ y ∉ U, ε ≤ D x y := by
  let : MetricSpace ClearancePoint := {
    dist := fun x y => D x.val y.val
    dist_self := fun x => hD.self_eq_zero x.val
    dist_comm := fun x y => hD.symm x.val y.val
    dist_triangle := fun x y z => hD.triangle x.val y.val z.val
    eq_of_dist_eq_zero := by
      intro ⟨x⟩ ⟨y⟩ h
      exact congrArg ClearancePoint.mk (hD.eq_of_eq_zero x y h) }
  have hmk : Continuous (fun x : ℂ => (⟨x⟩ : ClearancePoint)) := by
    rw [Metric.continuous_iff]
    intro x ε hε
    obtain ⟨δ, hδ, hbound⟩ := (Metric.continuous_iff.mp (hD.continuous_left x)) x ε hε
    refine ⟨δ, hδ, ?_⟩
    intro y hy
    have h := hbound y hy
    simp only [hD.self_eq_zero, Real.dist_eq, sub_zero] at h
    change D y x < ε
    exact lt_of_le_of_lt (le_abs_self _) h
  let K' : Set ClearancePoint := (fun x : ℂ => (⟨x⟩ : ClearancePoint)) '' K
  let U' : Set ClearancePoint := {x | x.val ∈ U}
  have hK' : IsCompact K' := hK.image hmk
  have hU' : IsOpen U' := by
    rw [Metric.isOpen_iff]
    rintro ⟨x⟩ hx
    obtain ⟨ε, hε, hball⟩ := (hD.isOpen_iff U).mp hU x hx
    refine ⟨ε, hε, ?_⟩
    rintro ⟨y⟩ hy
    apply hball
    change D y x < ε at hy
    simpa only [hD.symm y x] using hy
  have hdisjoint : Disjoint K' U'ᶜ := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hy
    exact hy (hKU hx)
  obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist hK' hU'.isClosed_compl hdisjoint
  refine ⟨r, by exact_mod_cast hr, ?_⟩
  intro x hx y hy
  have hxy := hsep (⟨x⟩ : ClearancePoint) ⟨x, hx, rfl⟩ ⟨y⟩ hy
  rw [edist_dist] at hxy
  exact (ENNReal.coe_lt_ofReal.mp hxy).le

/-- A path contained in an open set has a positive uniform distance to its
complement. -/
theorem IsEuclideanLengthMetric.path_uniform_boundary_clearance
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U : Set ℂ} (hU : IsOpen U) {x y : ℂ} (p : Path x y)
    (hp : ∀ t, p t ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, ∀ z ∉ U, ε ≤ D (p t) z := by
  have hK : IsCompact (range p) := isCompact_range p.continuous
  have hKU : range p ⊆ U := by rintro _ ⟨t, rfl⟩; exact hp t
  obtain ⟨ε, hε, hclear⟩ := hD.exists_uniform_boundary_clearance hK hU hKU
  exact ⟨ε, hε, fun t z hz => hclear _ ⟨t, rfl⟩ z hz⟩

end HarmonicBalls
