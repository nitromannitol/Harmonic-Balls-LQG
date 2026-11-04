import HarmonicBalls.Proofs.Sec10.ContinuumBoundaryBumping
import HarmonicBalls.Proofs.Sec10.LocalConnectivityBoundary

/-!
# Finite crossing families and local connectivity

A finite family of components covering a neighborhood gives a connected
relative neighborhood. For compact continua, boundary bumping supplies such
families from finite crossing counts.
-/

namespace HarmonicBalls

open Metric Set Filter Topology

/-- If finitely many components of a ball cover a smaller relative ball,
the component of the center is a relative neighborhood of the center. -/
theorem connectedComponentIn_mem_nhdsWithin_of_finite_cover
    {F : Set ℂ} (hF : IsClosed F) {x : ℂ}
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {S : Set (Set ℂ)} (hS : S.Finite)
    (hcomp : S ⊆ connectedComponentsIn (F ∩ ball x R))
    (hcover : F ∩ ball x r ⊆ ⋃₀ S) :
    connectedComponentIn (F ∩ ball x R) x ∈ 𝓝[F] x := by
  classical
  let C := connectedComponentIn (F ∩ ball x R) x
  let T := S \ {C}
  let A := ⋃ D ∈ T, closure D
  have hAclosed : IsClosed A := hS.subset (sdiff_subset) |>.isClosed_biUnion
    (fun D hD => isClosed_closure)
  have hxball : x ∈ ball x R := mem_ball_self (hr.trans hrR)
  have hxA : x ∉ A := by
    intro h
    obtain ⟨D, hD, hxD⟩ := mem_iUnion₂.mp h
    obtain ⟨y, hy, hyD⟩ := hcomp hD.1
    have hxD' : x ∈ D := by
      rw [← hyD, connectedComponentIn_eq_closure_inter_of_isClosed hF hy]
      exact ⟨by simpa only [hyD] using hxD, hxball⟩
    have heq : D = C := by
      rw [← hyD]
      exact connectedComponentIn_eq (hyD ▸ hxD')
    exact hD.2 (by simpa only [mem_singleton_iff] using heq)
  have hnear : ball x r ∩ Aᶜ ∈ 𝓝 x :=
    inter_mem (ball_mem_nhds x hr) (hAclosed.isOpen_compl.mem_nhds hxA)
  apply mem_of_superset (inter_mem (nhdsWithin_le_nhds hnear) self_mem_nhdsWithin)
  rintro y ⟨⟨hyr, hyA⟩, hyF⟩
  obtain ⟨D, hDS, hyD⟩ := mem_sUnion.mp (hcover ⟨hyF, hyr⟩)
  have hDC : D = C := by
    by_contra hne
    exact hyA (mem_iUnion₂.mpr ⟨D, ⟨hDS, by simpa only [mem_singleton_iff] using hne⟩,
      subset_closure hyD⟩)
  simpa only [hDC] using hyD

/-- In a compact continuum meeting the exterior of a ball, every component
that meets a smaller concentric ball crosses the two boundary circles. -/
theorem IsConnected.ball_component_crosses_of_meets_inner_ball
    {F : Set ℂ} (hF : IsConnected F) (hFcompact : IsCompact F)
    {x : ℂ} {r R : ℝ} (hrR : r < R)
    (hout : (F \ ball x R).Nonempty)
    {C : Set ℂ} (hC : C ∈ connectedComponentsIn (F ∩ ball x R))
    (hinner : (C ∩ ball x r).Nonempty) : CrossesAnnulus C x r R := by
  obtain ⟨y, hy, hyC⟩ := hC
  obtain ⟨z, hzC, hzr⟩ := hinner
  have hconn : IsConnected C := by rw [← hyC]; exact isConnected_connectedComponentIn_iff.mpr hy
  obtain ⟨q, hqcl, _, hqout⟩ :=
    IsConnected.closure_component_inter_open_meets_compl hF hFcompact isOpen_ball hout hy
  have hqcl' : q ∈ closure C := by simpa only [hyC] using hqcl
  have hsub : closure C ⊆ closedBall x R := by
    apply closure_minimal _ isClosed_closedBall
    intro v hv
    rw [← hyC] at hv
    exact ball_subset_closedBall (connectedComponentIn_subset _ y hv).2
  have hqR : dist q x = R := le_antisymm (mem_closedBall.mp (hsub hqcl'))
    (le_of_not_gt (fun hlt => hqout (mem_ball.mpr hlt)))
  obtain ⟨p, hpC, hpr⟩ := hconn.closure.isPreconnected.intermediate_value
    (subset_closure hzC) hqcl' (continuous_id.dist continuous_const).continuousOn
    ⟨(mem_ball.mp hzr).le, by simpa only [id_eq, hqR] using hrR.le⟩
  exact ⟨⟨p, hpC, mem_sphere.mpr hpr⟩, ⟨q, hqcl', mem_sphere.mpr hqR⟩⟩

/-- A finite crossing family makes the center's ball component a relative
neighborhood in a compact continuum. -/
theorem IsConnected.ball_component_mem_nhdsWithin_of_finite_crossings
    {F : Set ℂ} (hF : IsConnected F) (hFcompact : IsCompact F)
    {x : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hout : (F \ ball x R).Nonempty)
    (hfinite : (crossingComponents (F ∩ ball x R) x r R).Finite) :
    connectedComponentIn (F ∩ ball x R) x ∈ 𝓝[F] x := by
  apply connectedComponentIn_mem_nhdsWithin_of_finite_cover hFcompact.isClosed hr hrR hfinite
  · exact fun C hC => hC.1
  · intro y hy
    have hyR : y ∈ F ∩ ball x R := ⟨hy.1, ball_subset_ball hrR.le hy.2⟩
    let C := connectedComponentIn (F ∩ ball x R) y
    have hyC : y ∈ C := mem_connectedComponentIn hyR
    have hC : C ∈ connectedComponentsIn (F ∩ ball x R) := ⟨y, hyR, rfl⟩
    have hcross : CrossesAnnulus C x r R :=
      IsConnected.ball_component_crosses_of_meets_inner_ball hF hFcompact hrR hout hC
        ⟨y, hyC, hy.2⟩
    exact mem_sUnion.mpr ⟨C, ⟨hC, hcross⟩, hyC⟩

/-- A compact continuum is locally connected if, around each point and at
arbitrarily small scales, only finitely many ball components cross an inner
and outer circle. The exterior-point condition is explicit. -/
theorem IsConnected.isLocallyConnectedSet_of_finite_crossings
    {F : Set ℂ} (hF : IsConnected F) (hFcompact : IsCompact F)
    (hsmall : ∀ x ∈ F, ∀ δ : ℝ, 0 < δ → ∃ r R : ℝ,
      0 < r ∧ r < R ∧ R < δ ∧ (F \ ball x R).Nonempty ∧
        (crossingComponents (F ∩ ball x R) x r R).Finite) :
    IsLocallyConnectedSet F := by
  intro x hx N hN
  obtain ⟨δ, hδ, hδN⟩ := Metric.mem_nhdsWithin_iff.mp hN
  obtain ⟨r, R, hr, hrR, hRδ, hout, hfinite⟩ := hsmall x hx δ hδ
  let C := connectedComponentIn (F ∩ ball x R) x
  have hxR : x ∈ F ∩ ball x R := ⟨hx, mem_ball_self (hr.trans hrR)⟩
  refine ⟨C, IsConnected.ball_component_mem_nhdsWithin_of_finite_crossings
    hF hFcompact hr hrR hout hfinite, ?_, isConnected_connectedComponentIn_iff.mpr hxR⟩
  intro y hy
  have hy' := connectedComponentIn_subset (F ∩ ball x R) x hy
  exact ⟨hδN ⟨ball_subset_ball hRδ.le hy'.2, hy'.1⟩, hy'.1⟩

/-- A closed set is locally connected if, at each frontier point and arbitrarily
small scales, its ball components meeting the inner ball cross both circles and there are
finitely many such crossings. This form applies to unbounded closed sets. -/
theorem isLocallyConnectedSet_of_finite_crossings_and_escape
    {F : Set ℂ} (hF : IsClosed F)
    (hsmall : ∀ x ∈ F ∩ frontier F, ∀ δ : ℝ, 0 < δ → ∃ r R : ℝ,
      0 < r ∧ r < R ∧ R < δ ∧
      (crossingComponents (F ∩ ball x R) x r R).Finite ∧
      (∀ C ∈ connectedComponentsIn (F ∩ ball x R),
        (C ∩ ball x r).Nonempty → CrossesAnnulus C x r R)) :
    IsLocallyConnectedSet F := by
  apply (isLocallyConnectedSet_iff_frontier F).2
  intro x hx N hN
  obtain ⟨δ, hδ, hδN⟩ := Metric.mem_nhdsWithin_iff.mp hN
  obtain ⟨r, R, hr, hrR, hRδ, hfinite, hescape⟩ := hsmall x hx δ hδ
  let C := connectedComponentIn (F ∩ ball x R) x
  have hxR : x ∈ F ∩ ball x R := ⟨hx.1, mem_ball_self (hr.trans hrR)⟩
  have hcover : F ∩ ball x r ⊆ ⋃₀ crossingComponents (F ∩ ball x R) x r R := by
    intro y hy
    have hyR : y ∈ F ∩ ball x R := ⟨hy.1, ball_subset_ball hrR.le hy.2⟩
    let D := connectedComponentIn (F ∩ ball x R) y
    have hyD : y ∈ D := mem_connectedComponentIn hyR
    have hD : D ∈ connectedComponentsIn (F ∩ ball x R) := ⟨y, hyR, rfl⟩
    exact mem_sUnion.mpr ⟨D, ⟨hD, hescape D hD ⟨y, hyD, hy.2⟩⟩, hyD⟩
  have hnear : C ∈ 𝓝[F] x :=
    connectedComponentIn_mem_nhdsWithin_of_finite_cover hF hr hrR hfinite
      (fun D hD => hD.1) hcover
  refine ⟨C, hnear, ?_, isConnected_connectedComponentIn_iff.mpr hxR⟩
  intro y hy
  have hy' := connectedComponentIn_subset (F ∩ ball x R) x hy
  exact ⟨hδN ⟨ball_subset_ball hRδ.le hy'.2, hy'.1⟩, hy'.1⟩

end HarmonicBalls
