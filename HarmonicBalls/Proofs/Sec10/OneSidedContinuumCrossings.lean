import HarmonicBalls.Proofs.Sec10.ContinuumBoundaryBumping

/-!
# One-sided crossing components of compact continua

Boundary bumping yields a crossing component in either one-sided region:
inside the outer ball, or outside the inner closed ball. Passing to a single
component of their intersection remains a separate two-sided problem.
-/

namespace HarmonicBalls

open Metric Set Topology

/-- The component containing an inner-circle point crosses to the outer circle
inside the outer ball. -/
theorem IsConnected.ball_component_crosses_of_inner_point
    {K : Set ℂ} (hK : IsConnected K) (hKcompact : IsCompact K)
    (w : ℂ) {r R : ℝ} (hrR : r < R) (hKball : K ⊆ closedBall w R)
    (houter : (K ∩ sphere w R).Nonempty) {x : ℂ} (hxK : x ∈ K)
    (hxsphere : x ∈ sphere w r) :
    CrossesAnnulus (connectedComponentIn (K ∩ ball w R) x) w r R := by
  have hxball : x ∈ ball w R := mem_ball.mpr (by rw [mem_sphere.mp hxsphere]; exact hrR)
  have hout : (K \ ball w R).Nonempty := by
    obtain ⟨a, haK, haR⟩ := houter
    refine ⟨a, haK, ?_⟩
    intro ha
    have := mem_ball.mp ha
    rw [mem_sphere.mp haR] at this
    exact lt_irrefl R this
  obtain ⟨y, hycl, hyK, hyout⟩ :=
    IsConnected.closure_component_inter_open_meets_compl hK hKcompact isOpen_ball hout ⟨hxK, hxball⟩
  have hyR : y ∈ sphere w R := by
    apply mem_sphere.mpr
    exact le_antisymm (mem_closedBall.mp (hKball hyK))
      (le_of_not_gt (fun hlt => hyout (mem_ball.mpr hlt)))
  exact ⟨⟨x, subset_closure (mem_connectedComponentIn ⟨hxK, hxball⟩), hxsphere⟩,
    ⟨y, hycl, hyR⟩⟩

/-- The component containing an outer-circle point crosses to the inner
circle outside the inner closed ball. -/
theorem IsConnected.exterior_component_crosses_of_outer_point
    {K : Set ℂ} (hK : IsConnected K) (hKcompact : IsCompact K)
    (w : ℂ) {r R : ℝ} (hrR : r < R)
    (hinner : (K ∩ sphere w r).Nonempty) {x : ℂ} (hxK : x ∈ K)
    (hxsphere : x ∈ sphere w R) :
    CrossesAnnulus (connectedComponentIn (K ∩ (closedBall w r)ᶜ) x) w r R := by
  have hxext : x ∈ (closedBall w r)ᶜ := by
    rw [mem_compl_iff, mem_closedBall, not_le, mem_sphere.mp hxsphere]
    exact hrR
  have hout : (K \ (closedBall w r)ᶜ).Nonempty := by
    obtain ⟨a, haK, har⟩ := hinner
    refine ⟨a, haK, ?_⟩
    simpa only [mem_compl_iff, not_not] using
      (mem_closedBall.mpr (le_of_eq (mem_sphere.mp har)))
  obtain ⟨y, hycl, _, hyout⟩ :=
    IsConnected.closure_component_inter_open_meets_compl hK hKcompact
      isClosed_closedBall.isOpen_compl hout ⟨hxK, hxext⟩
  have hyclosed : y ∈ closedBall w r := by simpa only [mem_compl_iff, not_not] using hyout
  have hyr : r ≤ dist y w := by
    have hsub : connectedComponentIn (K ∩ (closedBall w r)ᶜ) x ⊆ (ball w r)ᶜ := by
      intro z hz hzb
      exact (connectedComponentIn_subset _ x hz).2 (ball_subset_closedBall hzb)
    have hynot : y ∈ (ball w r)ᶜ := closure_minimal hsub isOpen_ball.isClosed_compl hycl
    exact le_of_not_gt (fun hlt => hynot (mem_ball.mpr hlt))
  have hysphere : y ∈ sphere w r := mem_sphere.mpr (le_antisymm (mem_closedBall.mp hyclosed) hyr)
  exact ⟨⟨y, hycl, hysphere⟩,
    ⟨x, subset_closure (mem_connectedComponentIn ⟨hxK, hxext⟩), hxsphere⟩⟩

end HarmonicBalls
