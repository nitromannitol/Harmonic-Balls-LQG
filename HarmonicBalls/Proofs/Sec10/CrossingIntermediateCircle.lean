import HarmonicBalls.Proofs.Sec10.CrossingLocalization

/-!
# Crossing components and intermediate circles

A connected crossing meets each intermediate circle. Consequently it contains
an annular component meeting that circle. Showing that one such component
crosses the full annulus remains the separate boundary-bumping step.
-/

namespace HarmonicBalls

open Metric Set Topology

/-- A preconnected set whose closure meets both boundary circles meets every
intermediate circle. -/
theorem IsPreconnected.exists_mem_sphere_of_crosses
    {C : Set ℂ} (hC : IsPreconnected C) {w : ℂ} {r s R : ℝ}
    (hrs : r < s) (hsR : s < R) (hcross : CrossesAnnulus C w r R) :
    ∃ x ∈ C, x ∈ sphere w s := by
  obtain ⟨⟨a, ha, har⟩, ⟨b, hb, hbR⟩⟩ := hcross
  have haS : a ∈ ball w s := mem_ball.mpr (by rw [mem_sphere.mp har]; exact hrs)
  have hbS : b ∈ (closedBall w s)ᶜ := by
    rw [mem_compl_iff, mem_closedBall, not_le, mem_sphere.mp hbR]
    exact hsR
  obtain ⟨a', ha's, ha'C⟩ := mem_closure_iff.mp ha _ isOpen_ball haS
  obtain ⟨b', hb's, hb'C⟩ := mem_closure_iff.mp hb _ isClosed_closedBall.isOpen_compl hbS
  have ha' : dist a' w ≤ s := (mem_ball.mp ha's).le
  have hb' : s ≤ dist b' w := le_of_lt (by simpa [mem_closedBall, not_le] using hb's)
  obtain ⟨x, hxC, hxs⟩ := hC.intermediate_value ha'C hb'C
    (continuous_id.dist continuous_const).continuousOn ⟨ha', hb'⟩
  exact ⟨x, hxC, mem_sphere.mpr hxs⟩

/-- Each ball crossing contains an annular component meeting any prescribed
intermediate circle. This alone does not assert that the component crosses. -/
theorem exists_annular_component_meeting_intermediate_sphere
    (F : Set ℂ) (w : ℂ) {r s R : ℝ} (hrs : r < s) (hsR : s < R)
    {C : Set ℂ} (hC : C ∈ crossingComponents (F ∩ ball w R) w r R) :
    ∃ D ∈ connectedComponentsIn (F ∩ annulus w r R),
      D ⊆ C ∧ (D ∩ sphere w s).Nonempty := by
  obtain ⟨y, hy, hyC⟩ := hC.1
  have hconn : IsPreconnected C := by rw [← hyC]; exact isPreconnected_connectedComponentIn
  obtain ⟨x, hxC, hxs⟩ := IsPreconnected.exists_mem_sphere_of_crosses hconn hrs hsR hC.2
  have hxFB : x ∈ F ∩ ball w R := connectedComponentIn_subset _ y (hyC ▸ hxC)
  have hxann : x ∈ F ∩ annulus w r R := by
    refine ⟨hxFB.1, hxFB.2, ?_⟩
    rw [mem_closedBall, mem_sphere.mp hxs, not_le]
    exact hrs
  let D := connectedComponentIn (F ∩ annulus w r R) x
  have hDC : D ⊆ C := by
    rw [← hyC]
    apply connectedComponentIn_mono_of_mem (show F ∩ annulus w r R ⊆ F ∩ ball w R from
      fun _ h => ⟨h.1, h.2.1⟩) hxann
    exact hyC ▸ hxC
  exact ⟨D, ⟨x, hxann, rfl⟩, hDC, ⟨x, mem_connectedComponentIn hxann, hxs⟩⟩

/-- Distinct crossing components of the ball give distinct annular components
meeting a fixed intermediate circle, even without boundary bumping. -/
theorem encard_ball_crossings_le_annular_components_meeting_sphere
    (F : Set ℂ) (w : ℂ) {r s R : ℝ} (hrs : r < s) (hsR : s < R) :
    (crossingComponents (F ∩ ball w R) w r R).encard ≤
      {D ∈ connectedComponentsIn (F ∩ annulus w r R) |
        (D ∩ sphere w s).Nonempty}.encard := by
  classical
  let S := crossingComponents (F ∩ ball w R) w r R
  let T := {D ∈ connectedComponentsIn (F ∩ annulus w r R) |
    (D ∩ sphere w s).Nonempty}
  have hex : ∀ C ∈ S, ∃ D ∈ T, D ⊆ C := by
    intro C hC
    obtain ⟨D, hD, hsub, hmeet⟩ :=
      exists_annular_component_meeting_intermediate_sphere F w hrs hsR hC
    exact ⟨D, ⟨hD, hmeet⟩, hsub⟩
  let pick : Set ℂ → Set ℂ := fun C => if hC : C ∈ S then
    Classical.choose (hex C hC) else ∅
  have hpick : ∀ C ∈ S, pick C ∈ T ∧ pick C ⊆ C := by
    intro C hC
    simpa [pick, hC] using Classical.choose_spec (hex C hC)
  apply Set.encard_le_encard_of_injOn (fun C hC => (hpick C hC).1)
  intro C hC D hD heq
  by_contra hne
  have hdisj := pairwiseDisjoint_connectedComponentsIn (F ∩ ball w R) hC.1 hD.1 hne
  obtain ⟨x, hx, _⟩ := (hpick C hC).1.2
  exact Set.disjoint_left.mp hdisj ((hpick C hC).2 hx) ((hpick D hD).2 (heq ▸ hx))

end HarmonicBalls
