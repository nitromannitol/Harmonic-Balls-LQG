import HarmonicBalls.Defs.Notation
import Mathlib.Topology.MetricSpace.Thickening

/-!
# A circle separated from the origin

The grid in Proposition 6.1 excludes a neighbourhood of the origin. For the
proof of Proposition 7.1 we choose one of two radii so that the enclosing
circle stays uniformly separated from the origin, even if the original circle
passes through it.
-/

namespace HarmonicBalls

open Metric Set

/-- One of two intermediate radii is uniformly separated from any prescribed
nonnegative distance. -/
theorem exists_radius_separated_from_distance {r : ℝ} (hr : 0 < r) (d : ℝ) :
    ∃ q : ℝ, r / 4 < q ∧ q < r / 2 ∧ r / 32 ≤ |q - d| := by
  by_cases h : d ≤ 3 * r / 8
  · refine ⟨7 * r / 16, by linarith, by linarith, ?_⟩
    rw [abs_of_nonneg (by linarith)]
    linarith
  · refine ⟨5 * r / 16, by linarith, by linarith, ?_⟩
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- Choose a circle well inside `B_{r/2}(z)` and at distance at least `r/32`
from the origin. -/
theorem exists_origin_separated_sphere {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∃ q : ℝ, r / 4 < q ∧ q < r / 2 ∧
      ∀ y ∈ sphere z q, r / 32 ≤ dist y (0 : ℂ) := by
  obtain ⟨q, hq₁, hq₂, hsep⟩ := exists_radius_separated_from_distance hr (dist z 0)
  refine ⟨q, hq₁, hq₂, fun y hy => ?_⟩
  have hyq : dist y z = q := mem_sphere.1 hy
  have hd := abs_dist_sub_le y (0 : ℂ) z
  rw [hyq, dist_comm (0 : ℂ) z] at hd
  exact hsep.trans hd

/-- A ball around a sufficiently close centre stays inside the unit domain and
avoids the pole when the inner and outer radial margins are positive. -/
theorem closedBall_subset_unitBall_sdiff_pole_of_near_sphere
    {z y x : ℂ} {q δ ρ : ℝ} (hy : y ∈ sphere z q)
    (hclose : dist x y < δ) (hinner : δ + ρ < q)
    (houter : dist z 0 + q + δ + ρ < 1) :
    closedBall x ρ ⊆ ball 0 1 \ {z} := by
  have hyq : dist y z = q := mem_sphere.1 hy
  intro w hw
  have hwx : dist w x ≤ ρ := mem_closedBall.1 hw
  have hxy0 := dist_triangle x y (0 : ℂ)
  have hyz0 := dist_triangle y z (0 : ℂ)
  have hwx0 := dist_triangle w x (0 : ℂ)
  constructor
  · rw [mem_ball]
    linarith
  · intro hwz
    have : w = z := by simpa using hwz
    subst w
    have htriangle := dist_triangle y x z
    rw [dist_comm y x, dist_comm x z] at htriangle
    linarith

/-- If the origin lies in the cluster closure, every point outside its inner
thickening is at least that far from the origin. This is the boundary case in
the origin-exclusion repair for the shell cover in Proposition 7.2. -/
theorem radius_le_dist_zero_of_not_mem_thickening
    {A : Set ℂ} {r : ℝ} (hA : A.Nonempty) (hzero : (0 : ℂ) ∈ closure A)
    {y : ℂ} (hy : y ∉ thickening r A) : r ≤ dist y 0 := by
  have hdist : r ≤ infDist y A := by
    rw [mem_thickening_iff_infDist_lt hA] at hy
    exact le_of_not_gt hy
  have hzdist : infDist y A ≤ dist y 0 := by
    rw [← infDist_closure]
    exact infDist_le_dist_of_mem hzero
  exact hdist.trans hzdist

end HarmonicBalls
