import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Steps.Sec11.PinchConstrainedFiniteness

/-!
# Proposition 11.9, finiteness of the internal metric on a preconnected open set

Used for the exterior bound `sup_{u,v ∈ V \ S₂} D_h(u,v; O) ≤ A` (paper line 3120): the set `V \ S₂` is open
and preconnected (`PlaneDomainMinusConvexCompactPreconnectedFrozen`), so any two of its points are joined inside `O`, hence
their internal distance in `O` is finite (`IsEuclideanLengthMetric.internalMetric_lt_top_of_joinedIn`).
-/

namespace HarmonicBalls

open Set

/-- Two points of an open preconnected set `A ⊆ O` are joined by a path inside `O`, so their internal distance in `O` is finite. -/
theorem internalMetric_lt_top_of_mem_preconnected {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {O A : Set ℂ} (hO : IsOpen O) (hA : IsOpen A) (hAc : IsPreconnected A)
    (hAO : A ⊆ O) {u v : ℂ} (hu : u ∈ A) (hv : v ∈ A) :
    internalMetric D O u v < ⊤ := by
  have hconn : IsConnected A := ⟨⟨u, hu⟩, hAc⟩
  have hpath : IsPathConnected A := (hA.isConnected_iff_isPathConnected).mp hconn
  have hjoin : JoinedIn A u v := hpath.joinedIn u hu v hv
  exact hD.internalMetric_lt_top_of_joinedIn hnonneg hO (hjoin.mono hAO)

end HarmonicBalls
