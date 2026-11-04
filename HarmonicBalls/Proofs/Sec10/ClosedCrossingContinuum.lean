import HarmonicBalls.Proofs.Sec10.CrossingIntermediateCircle

/-!
# Compact continua from crossings of closed sets

For a closed set, a component of its intersection with a ball contains every
point of its closure which still lies in that ball. Its closure is therefore a
compact connected crossing, and the inner-circle contact belongs to the
component itself. This is a reduction towards annular boundary bumping.
-/

namespace HarmonicBalls

open Metric Set Topology

/-- A component of `F ∩ O`, with `F` closed, contains all points of its
closure which belong to `O`. -/
theorem connectedComponentIn_eq_closure_inter_of_isClosed
    {F O : Set ℂ} (hF : IsClosed F) {x : ℂ} (hx : x ∈ F ∩ O) :
    connectedComponentIn (F ∩ O) x = closure (connectedComponentIn (F ∩ O) x) ∩ O := by
  let C := connectedComponentIn (F ∩ O) x
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hCF : C ⊆ F := fun _ hy => (connectedComponentIn_subset _ x hy).1
  have hCO : C ⊆ O := fun _ hy => (connectedComponentIn_subset _ x hy).2
  apply Subset.antisymm
  · exact fun _ hy => ⟨subset_closure hy, hCO hy⟩
  · intro y hy
    have hyF : y ∈ F := closure_minimal hCF hF hy.1
    have hconn : IsPreconnected (C ∪ {y}) :=
      isPreconnected_connectedComponentIn.subset_closure (subset_union_left)
        (union_subset subset_closure (singleton_subset_iff.mpr hy.1))
    have hsub : C ∪ {y} ⊆ F ∩ O := by
      rintro z (hz | hz)
      · exact connectedComponentIn_subset _ x hz
      · have hz' : z = y := mem_singleton_iff.mp hz
        subst z
        exact ⟨hyF, hy.2⟩
    exact hconn.subset_connectedComponentIn (mem_union_left _ hxC) hsub (mem_union_right _ rfl)

/-- A crossing component of a closed set in a ball contains its inner-circle
contact, and its closure is a compact connected crossing in the closed ball. -/
theorem closed_ball_crossing_compact_continuum
    {F C : Set ℂ} (hF : IsClosed F) (w : ℂ) {r R : ℝ} (hrR : r < R)
    (hC : C ∈ crossingComponents (F ∩ ball w R) w r R) :
    IsCompact (closure C) ∧ IsConnected (closure C) ∧
      closure C ⊆ F ∩ closedBall w R ∧
      (C ∩ sphere w r).Nonempty ∧ CrossesAnnulus (closure C) w r R := by
  obtain ⟨x, hx, hxC⟩ := hC.1
  have hsub : C ⊆ F ∩ ball w R := by rw [← hxC]; exact connectedComponentIn_subset _ x
  have hclsub : closure C ⊆ F ∩ closedBall w R := by
    exact closure_minimal (fun y hy => ⟨(hsub hy).1, ball_subset_closedBall (hsub hy).2⟩)
      (hF.inter isClosed_closedBall)
  have hcompact : IsCompact (closure C) :=
    (isCompact_closedBall w R).of_isClosed_subset isClosed_closure (fun _ hy => (hclsub hy).2)
  have hconn : IsConnected C := by rw [← hxC]; exact isConnected_connectedComponentIn_iff.mpr hx
  have hinner : (C ∩ sphere w r).Nonempty := by
    obtain ⟨a, ha, has⟩ := hC.2.1
    have haball : a ∈ ball w R := mem_ball.mpr (by rw [mem_sphere.mp has]; exact hrR)
    have haC : a ∈ C := by
      rw [← hxC, connectedComponentIn_eq_closure_inter_of_isClosed hF hx]
      exact ⟨by simpa only [hxC] using ha, haball⟩
    exact ⟨a, haC, has⟩
  have hcross : CrossesAnnulus (closure C) w r R := by
    simpa only [CrossesAnnulus, closure_closure] using hC.2
  exact ⟨hcompact, hconn.closure, hclsub, hinner, hcross⟩

/-- Boundary bumping for compact connected crossings implies the component
containment needed for crossings of arbitrary closed sets. -/
theorem closed_ball_crossing_contains_annular_crossing_of_compact_continuum
    {F : Set ℂ} (hF : IsClosed F) (w : ℂ) {r R : ℝ} (hrR : r < R)
    (hcompactBump : ∀ K : Set ℂ, IsCompact K → IsConnected K →
      K ⊆ closedBall w R → CrossesAnnulus K w r R →
      (crossingComponents (K ∩ annulus w r R) w r R).Nonempty)
    {C : Set ℂ} (hC : C ∈ crossingComponents (F ∩ ball w R) w r R) :
    ∃ D ∈ crossingComponents (F ∩ annulus w r R) w r R, D ⊆ C := by
  obtain ⟨hcompact, hconn, hsub, _, hcross⟩ :=
    closed_ball_crossing_compact_continuum hF w hrR hC
  obtain ⟨E, hE⟩ := hcompactBump (closure C) hcompact hconn (fun _ hy => (hsub hy).2) hcross
  obtain ⟨x, hx, hxE⟩ := hE.1
  have hxFann : x ∈ F ∩ annulus w r R := ⟨(hsub hx.1).1, hx.2⟩
  let D := connectedComponentIn (F ∩ annulus w r R) x
  have hED : E ⊆ D := by
    rw [← hxE]
    exact connectedComponentIn_mono x (fun _ hy => ⟨(hsub hy.1).1, hy.2⟩)
  have hxC : x ∈ C := by
    obtain ⟨y, hy, hyC⟩ := hC.1
    rw [← hyC, connectedComponentIn_eq_closure_inter_of_isClosed hF hy]
    exact ⟨by simpa only [hyC] using hx.1, hx.2.1⟩
  have hDC : D ⊆ C := by
    obtain ⟨y, hy, hyC⟩ := hC.1
    rw [← hyC]
    apply connectedComponentIn_mono_of_mem
      (show F ∩ annulus w r R ⊆ F ∩ ball w R from fun _ hz => ⟨hz.1, hz.2.1⟩) hxFann
    exact hyC ▸ hxC
  have hDcross : CrossesAnnulus D w r R := by
    obtain ⟨⟨a, ha, har⟩, ⟨b, hb, hbR⟩⟩ := hE.2
    exact ⟨⟨a, closure_mono hED ha, har⟩, ⟨b, closure_mono hED hb, hbR⟩⟩
  exact ⟨D, ⟨⟨x, hxFann, rfl⟩, hDcross⟩, hDC⟩

end HarmonicBalls
