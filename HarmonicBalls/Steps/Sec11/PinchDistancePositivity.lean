import HarmonicBalls.Steps.Sec11.CompactBoundaryClearance

/-! # Positive distances in the auxiliary pinch events

Compact Euclidean separation gives positive distance for any length metric
which induces the Euclidean topology.
-/

namespace HarmonicBalls

open Set Metric

/-- A nonempty compact set in an open set has positive set distance to any
nonempty subset of its complement. -/
theorem IsEuclideanLengthMetric.setDist_pos_of_compact_subset_open
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {K U B : Set ℂ} (hK : IsCompact K) (hneK : K.Nonempty)
    (hU : IsOpen U) (hKU : K ⊆ U) (hneB : B.Nonempty) (hBU : B ⊆ Uᶜ) :
    0 < setDist D K B := by
  obtain ⟨ε, hε, hsep⟩ := hD.exists_uniform_boundary_clearance hK hU hKU
  apply hε.trans_le
  unfold setDist
  apply le_csInf
  · obtain ⟨x, hx⟩ := hneK
    obtain ⟨y, hy⟩ := hneB
    exact ⟨D x y, Set.mem_image2_of_mem hx hy⟩
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    exact hsep x hx y (hBU hy)

/-- Concentric Euclidean spheres of different positive radii have positive
set distance in any Euclidean length metric. -/
theorem IsEuclideanLengthMetric.setDist_spheres_pos
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (z : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    0 < setDist D (sphere z r) (sphere z R) := by
  apply hD.setDist_pos_of_compact_subset_open (isCompact_sphere z r)
    (NormedSpace.sphere_nonempty.mpr hr.le) isOpen_ball
  · intro x hx
    rw [mem_ball, mem_sphere] at *
    linarith
  · exact NormedSpace.sphere_nonempty.mpr (by linarith)
  · intro x hx hball
    rw [mem_sphere] at hx
    rw [mem_ball] at hball
    linarith

/-- The two sphere distances used in the auxiliary pinch events are positive. -/
theorem IsEuclideanLengthMetric.pinch_sphere_distances_pos
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {δ : ℝ} (hδ : 0 < δ) :
    0 < setDist D (sphere 0 δ) (sphere 0 (2 * δ)) ∧
    0 < setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ)) := by
  exact ⟨hD.setDist_spheres_pos 0 hδ (by linarith),
    hD.setDist_spheres_pos 0 (by linarith) (by linarith)⟩

/-- In a pinch configuration the distance from `Q'` to the frontier of `Q`
is positive in every Euclidean length metric. -/
theorem IsPinchPointConfiguration.setDist_frontier_pos
    {U T Q' Q : Set ℂ} (h : IsPinchPointConfiguration U T Q' Q)
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) :
    0 < setDist D Q' (frontier Q) := by
  have hQ'Q : Q' ⊆ Q := subset_closure.trans h.closure_Q'_subset
  have hbound : Bornology.IsBounded Q' := by
    apply (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) 5)).subset
    intro x hx
    exact (h.Q_subset (hQ'Q hx)).1.1
  have hcompact : IsCompact (closure Q') :=
    isCompact_of_isClosed_isBounded isClosed_closure hbound.closure
  obtain ⟨ε, hε, hsep⟩ := hD.exists_uniform_boundary_clearance
    hcompact h.isOpen_Q h.closure_Q'_subset
  have hQne : Q ≠ univ := by
    intro heq
    have hzero : (0 : ℂ) ∈ Q := by rw [heq]; exact mem_univ _
    have hz := h.Q_subset hzero
    exact hz.1.2 (by simp)
  have hfront : (frontier Q).Nonempty :=
    nonempty_frontier_iff.mpr ⟨h.isConnected_Q.nonempty, hQne⟩
  apply hε.trans_le
  unfold setDist
  apply le_csInf
  · obtain ⟨x, hx⟩ := h.isConnected_Q'.nonempty
    obtain ⟨y, hy⟩ := hfront
    exact ⟨D x y, Set.mem_image2_of_mem hx hy⟩
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    apply hsep x (subset_closure hx) y
    rw [h.isOpen_Q.frontier_eq] at hy
    exact hy.2

end HarmonicBalls
