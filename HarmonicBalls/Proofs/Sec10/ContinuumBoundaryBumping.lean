import HarmonicBalls.Proofs.Sec10.CompactComponentSeparation

/-!
# Boundary bumping for compact connected subsets

The ambient boundary-bumping theorem applies to the subtype of a compact
connected set. Its image gives boundary contact for a component of the
intersection of that set with an open set.
-/

namespace HarmonicBalls

open Set Topology

/-- A component of the intersection of a compact connected set with an open
set has closure meeting the part of the compact set outside the open set. -/
theorem IsConnected.closure_component_inter_open_meets_compl
    {X : Type*} [TopologicalSpace X] [T2Space X] {K O : Set X}
    (hK : IsConnected K) (hKcompact : IsCompact K) (hO : IsOpen O)
    (houtside : (K \ O).Nonempty) {x : X} (hx : x ∈ K ∩ O) :
    (closure (connectedComponentIn (K ∩ O) x) ∩ (K \ O)).Nonempty := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  let : ConnectedSpace K := isConnected_iff_connectedSpace.mp hK
  let x' : K := ⟨x, hx.1⟩
  let O' : Set K := Subtype.val ⁻¹' O
  have hO' : IsOpen O' := hO.preimage continuous_subtype_val
  have hproper : O' ≠ univ := by
    obtain ⟨y, hyK, hyO⟩ := houtside
    intro h
    have hy : (⟨y, hyK⟩ : K) ∈ O' := by rw [h]; trivial
    exact hyO hy
  have hx' : x' ∈ O' := hx.2
  obtain ⟨y, hycl, hyO⟩ :=
    closure_connectedComponentIn_inter_compl_nonempty hO' hproper hx'
  have himage : Subtype.val '' connectedComponentIn O' x' ⊆ connectedComponentIn (K ∩ O) x := by
    have hconnected : IsPreconnected (Subtype.val '' connectedComponentIn O' x') :=
      isPreconnected_connectedComponentIn.image Subtype.val continuous_subtype_val.continuousOn
    have hximage : x ∈ Subtype.val '' connectedComponentIn O' x' :=
      ⟨x', mem_connectedComponentIn hx', rfl⟩
    have hsub : Subtype.val '' connectedComponentIn O' x' ⊆ K ∩ O := by
      rintro z ⟨a, ha, rfl⟩
      exact ⟨a.property, connectedComponentIn_subset O' x' ha⟩
    exact hconnected.subset_connectedComponentIn hximage hsub
  have hycl' : (y : X) ∈ closure (connectedComponentIn (K ∩ O) x) :=
    closure_mono himage (image_closure_subset_closure_image continuous_subtype_val ⟨y, hycl, rfl⟩)
  exact ⟨y, hycl', y.property, hyO⟩

/-- Every component of a compact continuum inside an annulus has closure
meeting at least one of its boundary circles, provided the continuum meets
its inner circle and stays inside the outer closed ball. -/
theorem IsConnected.annular_component_meets_boundary_circle
    {K : Set ℂ} (hK : IsConnected K) (hKcompact : IsCompact K)
    (w : ℂ) {r R : ℝ} (hKball : K ⊆ Metric.closedBall w R)
    (hinner : (K ∩ Metric.sphere w r).Nonempty)
    {x : ℂ} (hx : x ∈ K ∩ annulus w r R) :
    ∃ y ∈ closure (connectedComponentIn (K ∩ annulus w r R) x),
      y ∈ Metric.sphere w r ∨ y ∈ Metric.sphere w R := by
  have hO : IsOpen (annulus w r R) := Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
  have hout : (K \ annulus w r R).Nonempty := by
    obtain ⟨a, haK, has⟩ := hinner
    refine ⟨a, haK, ?_⟩
    intro ha
    have ha' : a ∈ Metric.closedBall w r :=
      Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp has))
    exact ha.2 ha'
  obtain ⟨y, hycl, hyK, hyO⟩ :=
    IsConnected.closure_component_inter_open_meets_compl hK hKcompact hO hout hx
  have hsub : connectedComponentIn (K ∩ annulus w r R) x ⊆ annulus w r R :=
    fun _ hz => (connectedComponentIn_subset _ x hz).2
  have hyR : dist y w ≤ R := Metric.mem_closedBall.mp (hKball hyK)
  have hyr : r ≤ dist y w := by
    have hyclosed : y ∈ (Metric.ball w r)ᶜ :=
      closure_minimal (fun z hz hzb => hz.2 (Metric.ball_subset_closedBall hzb))
        Metric.isOpen_ball.isClosed_compl (closure_mono hsub hycl)
    exact le_of_not_gt (fun hlt => hyclosed (Metric.mem_ball.mpr hlt))
  refine ⟨y, hycl, ?_⟩
  by_cases hyball : y ∈ Metric.ball w R
  · have hyinside : y ∈ Metric.closedBall w r := by
      by_contra hnot
      exact hyO ⟨hyball, hnot⟩
    left
    exact Metric.mem_sphere.mpr (le_antisymm (Metric.mem_closedBall.mp hyinside) hyr)
  · right
    have hyR' : R ≤ dist y w := le_of_not_gt (fun hlt => hyball (Metric.mem_ball.mpr hlt))
    exact Metric.mem_sphere.mpr (le_antisymm hyR hyR')

end HarmonicBalls
