import HarmonicBalls.Proofs.Sec10.FiniteContinuumCrossings
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Annular crossings with locally connected annular slice

Compact subsets of a locally connected space meet only finitely many connected
components. Applied to a middle circle, this gives the finite-crossing
hypothesis for the full annular crossing theorem.
-/

namespace HarmonicBalls

open Metric Set Topology

/-- Only finitely many components of a locally connected subspace meet a
compact subset of that subspace. -/
theorem finite_connectedComponentsIn_meeting_compact
    {X : Type*} [TopologicalSpace X] {F S : Set X}
    [LocallyConnectedSpace F] (hS : IsCompact S) (hSF : S ⊆ F) :
    {C ∈ connectedComponentsIn F | (C ∩ S).Nonempty}.Finite := by
  classical
  let T : Set F := Subtype.val ⁻¹' S
  have hT : IsCompact T := by
    rw [IsEmbedding.subtypeVal.isCompact_iff]
    simpa only [T, image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.mpr hSF]
      using hS
  let Q := ConnectedComponents.mk '' T
  have hQ : Q.Finite := (hT.image ConnectedComponents.continuous_coe).finite DiscreteTopology.isDiscrete
  let rep : ConnectedComponents F → F := fun q => Classical.choose (ConnectedComponents.surjective_coe q)
  have hrep (q : ConnectedComponents F) : ConnectedComponents.mk (rep q) = q :=
    Classical.choose_spec (ConnectedComponents.surjective_coe q)
  let components : ConnectedComponents F → Set X := fun q => connectedComponentIn F (rep q)
  apply (hQ.image components).subset
  intro C hC
  obtain ⟨⟨y, hyF, rfl⟩, x, hxC, hxS⟩ := hC
  have hxF : x ∈ F := hSF hxS
  have hcomponent : connectedComponentIn F x = connectedComponentIn F y :=
    (connectedComponentIn_eq hxC).symm
  let z : F := ⟨x, hxF⟩
  refine ⟨ConnectedComponents.mk z, ⟨z, hxS, rfl⟩, ?_⟩
  dsimp [components]
  have hq : ConnectedComponents.mk (rep (ConnectedComponents.mk z)) = ConnectedComponents.mk z :=
    hrep _
  have heq : connectedComponent (rep (ConnectedComponents.mk z)) = connectedComponent z :=
    ConnectedComponents.coe_eq_coe.mp hq
  calc
    connectedComponentIn F (rep (ConnectedComponents.mk z)) = connectedComponentIn F x := by
      rw [connectedComponentIn_eq_image (rep (ConnectedComponents.mk z)).property,
        connectedComponentIn_eq_image hxF, heq]
    _ = connectedComponentIn F y := hcomponent

/-- A compact continuum has a full annular crossing if its open annular slice
is locally connected. -/
theorem IsConnected.exists_annular_component_crossing_of_locallyConnected
    {K : Set ℂ} (hK : IsConnected K) (hKcompact : IsCompact K)
    (w : ℂ) {r R : ℝ} (hrR : r < R) (hcross : CrossesAnnulus K w r R)
    [LocallyConnectedSpace ↥(K ∩ annulus w r R)] :
    (crossingComponents (K ∩ annulus w r R) w r R).Nonempty := by
  let a := r + (R-r)/3
  let b := R - (R-r)/3
  let s := (r + R)/2
  have ha : r < a := by dsimp [a]; linarith
  have has : a < s := by dsimp [a, s]; linarith
  have hsb : s < b := by dsimp [b, s]; linarith
  have hb : b < R := by dsimp [b]; linarith
  have hSc : IsCompact (K ∩ sphere w s) := hKcompact.inter_right isClosed_sphere
  have hsub : K ∩ sphere w s ⊆ K ∩ annulus w r R := by
    intro x hx
    refine ⟨hx.1, mem_ball.mpr ?_, ?_⟩
    · rw [mem_sphere.mp hx.2]; linarith
    · rw [mem_closedBall, mem_sphere.mp hx.2, not_le]; linarith
  have hfinite := finite_connectedComponentsIn_meeting_compact hSc hsub
  have hcrossfinite : (crossingComponents (K ∩ annulus w r R) w a b).Finite := by
    apply hfinite.subset
    intro C hC
    have hconn : IsPreconnected C := by
      obtain ⟨x, hx, rfl⟩ := hC.1
      exact isPreconnected_connectedComponentIn
    obtain ⟨x, hxC, hxS⟩ := IsPreconnected.exists_mem_sphere_of_crosses hconn has hsb hC.2
    have hxK : x ∈ K := by
      obtain ⟨y, hy, hyC⟩ := hC.1
      have hxComp : x ∈ connectedComponentIn (K ∩ annulus w r R) y := by
        simpa only [hyC] using hxC
      exact (connectedComponentIn_subset (K ∩ annulus w r R) y hxComp).1
    exact ⟨hC.1, ⟨x, hxC, hxK, hxS⟩⟩
  exact IsConnected.exists_annular_component_crossing_of_finite hK hKcompact w hrR hcross hcrossfinite

/-- A closed set has only finitely many ball-crossing components when the
corresponding open annular slice is locally connected. -/
theorem closed_ball_crossings_finite_of_locallyConnected_annulus
    {F : Set ℂ} (hF : IsClosed F) (w : ℂ) {r R : ℝ} (hrR : r < R)
    [LocallyConnectedSpace ↥(F ∩ annulus w r R)] :
    (crossingComponents (F ∩ ball w R) w r R).Finite := by
  let s := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  have hSc : IsCompact (F ∩ sphere w s) := (isCompact_sphere w s).inter_left hF
  have hsub : F ∩ sphere w s ⊆ F ∩ annulus w r R := by
    intro x hx
    refine ⟨hx.1, mem_ball.mpr ?_, ?_⟩
    · rw [mem_sphere.mp hx.2]; exact hsR
    · rw [mem_closedBall, mem_sphere.mp hx.2, not_le]; exact hrs
  have hfinite := finite_connectedComponentsIn_meeting_compact hSc hsub
  have heq : {D ∈ connectedComponentsIn (F ∩ annulus w r R) |
      (D ∩ (F ∩ sphere w s)).Nonempty} =
      {D ∈ connectedComponentsIn (F ∩ annulus w r R) |
        (D ∩ sphere w s).Nonempty} := by
    ext D
    constructor
    · rintro ⟨hD, x, hxD, hxF, hxs⟩
      exact ⟨hD, x, hxD, hxs⟩
    · rintro ⟨hD, x, hxD, hxs⟩
      have hxF : x ∈ F := by
        obtain ⟨y, hy, hyD⟩ := hD
        have hxComp : x ∈ connectedComponentIn (F ∩ annulus w r R) y := by
          simpa only [hyD] using hxD
        exact (connectedComponentIn_subset _ y hxComp).1
      exact ⟨hD, x, hxD, hxF, hxs⟩
  rw [heq] at hfinite
  exact hfinite.finite_of_encard_le
    (encard_ball_crossings_le_annular_components_meeting_sphere F w hrs hsR)

end HarmonicBalls
