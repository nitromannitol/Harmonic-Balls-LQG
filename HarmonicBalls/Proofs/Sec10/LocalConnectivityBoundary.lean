import HarmonicBalls.Proofs.Sec10.ComplementComponents

/-!
# Local connectivity away from the frontier

At an interior point of a planar set, Euclidean balls give connected
neighborhoods relative to the set. Thus local connectivity only needs to be
checked at frontier points belonging to the set.
-/

namespace HarmonicBalls

open Metric Set Filter Topology

/-- Every relative neighborhood of an interior point contains a connected
relative neighborhood. -/
theorem exists_connected_relative_neighborhood_of_mem_interior
    {F : Set ℂ} {x : ℂ} (hx : x ∈ interior F)
    {N : Set ℂ} (hN : N ∈ 𝓝[F] x) :
    ∃ V ∈ 𝓝[F] x, V ⊆ N ∩ F ∧ IsConnected V := by
  have hF : F ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hx
  have hN' : N ∈ 𝓝 x := by rwa [nhdsWithin_eq_nhds.mpr hF] at hN
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hN' hF)
  refine ⟨ball x r, ?_, hrsub, isConnected_ball hr⟩
  exact nhdsWithin_le_nhds (ball_mem_nhds x hr)

/-- For a planar set it suffices to check local connectivity at the frontier
points which belong to the set. -/
theorem isLocallyConnectedSet_iff_frontier (F : Set ℂ) :
    IsLocallyConnectedSet F ↔
      ∀ x ∈ F ∩ frontier F, ∀ N ∈ 𝓝[F] x,
        ∃ V ∈ 𝓝[F] x, V ⊆ N ∩ F ∧ IsConnected V := by
  constructor
  · intro h x hx N hN
    exact h x hx.1 N hN
  · intro h x hx N hN
    by_cases hxint : x ∈ interior F
    · exact exists_connected_relative_neighborhood_of_mem_interior hxint hN
    · exact h x ⟨hx, (mem_frontier_iff_notMem_interior hx).mpr hxint⟩ N hN

/-- For an open set, local connectivity of its complement can be checked on
its frontier. -/
theorem isLocallyConnectedSet_compl_iff_frontier {U : Set ℂ} (hU : IsOpen U) :
    IsLocallyConnectedSet Uᶜ ↔
      ∀ x ∈ frontier U, ∀ N ∈ 𝓝[Uᶜ] x,
        ∃ V ∈ 𝓝[Uᶜ] x, V ⊆ N ∩ Uᶜ ∧ IsConnected V := by
  rw [isLocallyConnectedSet_iff_frontier]
  have hfront : frontier U ⊆ Uᶜ := by
    rw [hU.frontier_eq]
    exact sdiff_subset_compl _ _
  simp only [frontier_compl, inter_eq_right.mpr hfront]

end HarmonicBalls
