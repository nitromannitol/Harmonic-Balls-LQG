import HarmonicBalls.Proofs.Sec10.FiniteContinuumCrossings
import HarmonicBalls.Proofs.Sec10.ClosedCrossingContinuum

/-! # Closed-set crossings with finitely many interior crossings -/

namespace HarmonicBalls

open Metric Set Topology

/-- A ball crossing of a closed set contains a full annular crossing if the
annular components of its compact closure crossing the middle third are finite. -/
theorem closed_ball_crossing_contains_annular_crossing_of_finite
    {F C : Set ℂ} (hF : IsClosed F) (w : ℂ) {r R : ℝ} (hrR : r < R)
    (hC : C ∈ crossingComponents (F ∩ ball w R) w r R)
    (hfinite : (crossingComponents (closure C ∩ annulus w r R) w
      (r + (R-r)/3) (R - (R-r)/3)).Finite) :
    ∃ D ∈ crossingComponents (F ∩ annulus w r R) w r R, D ⊆ C := by
  obtain ⟨hcompact, hconn, hsub, _, hcross⟩ :=
    closed_ball_crossing_compact_continuum hF w hrR hC
  obtain ⟨E, hE⟩ := IsConnected.exists_annular_component_crossing_of_finite
    hconn hcompact w hrR hcross hfinite
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

/-- Finiteness of the middle-third crossings of the whole closed set is enough
for each of its ball-crossing components to contain a full annular crossing. -/
theorem closed_ball_crossing_contains_annular_crossing_of_global_finite
    {F C : Set ℂ} (hF : IsClosed F) (w : ℂ) {r R : ℝ} (hrR : r < R)
    (hC : C ∈ crossingComponents (F ∩ ball w R) w r R)
    (hfinite : (crossingComponents (F ∩ annulus w r R) w
      (r + (R-r)/3) (R - (R-r)/3)).Finite) :
    ∃ D ∈ crossingComponents (F ∩ annulus w r R) w r R, D ⊆ C := by
  obtain ⟨_, _, hsub, _, _⟩ := closed_ball_crossing_compact_continuum hF w hrR hC
  have hsubset : crossingComponents (closure C ∩ annulus w r R) w
      (r + (R-r)/3) (R - (R-r)/3) ⊆
      crossingComponents (F ∩ annulus w r R) w
      (r + (R-r)/3) (R - (R-r)/3) := by
    intro D hD
    obtain ⟨⟨x, hx, rfl⟩, hcross⟩ := hD
    have hxC : x ∈ C := by
      obtain ⟨y, hy, hyC⟩ := hC.1
      rw [← hyC, connectedComponentIn_eq_closure_inter_of_isClosed hF hy]
      exact ⟨by simpa only [hyC] using hx.1, hx.2.1⟩
    have hxF : x ∈ F ∩ annulus w r R := ⟨(hsub hx.1).1, hx.2⟩
    have hDC : connectedComponentIn (F ∩ annulus w r R) x ⊆ C := by
      obtain ⟨y, hy, hyC⟩ := hC.1
      rw [← hyC]
      apply connectedComponentIn_mono_of_mem
        (show F ∩ annulus w r R ⊆ F ∩ ball w R from fun _ hz => ⟨hz.1, hz.2.1⟩) hxF
      exact hyC ▸ hxC
    have heq : connectedComponentIn (closure C ∩ annulus w r R) x =
        connectedComponentIn (F ∩ annulus w r R) x := by
      apply Subset.antisymm
      · exact connectedComponentIn_mono x (fun _ hz => ⟨(hsub hz.1).1, hz.2⟩)
      · apply isPreconnected_connectedComponentIn.subset_connectedComponentIn
          (mem_connectedComponentIn hxF)
        intro z hz
        exact ⟨subset_closure (hDC hz), (connectedComponentIn_subset _ x hz).2⟩
    rw [heq] at hcross ⊢
    exact ⟨⟨x, hxF, rfl⟩, hcross⟩
  exact closed_ball_crossing_contains_annular_crossing_of_finite hF w hrR hC
    (hfinite.subset hsubset)

/-- Under middle-third finiteness, the number of ball crossings is bounded by
the number of full annular crossings. -/
theorem encard_ball_crossings_le_annular_crossings_of_finite
    {F : Set ℂ} (hF : IsClosed F) (w : ℂ) {r R : ℝ} (hrR : r < R)
    (hfinite : (crossingComponents (F ∩ annulus w r R) w
      (r + (R-r)/3) (R - (R-r)/3)).Finite) :
    (crossingComponents (F ∩ ball w R) w r R).encard ≤
      (crossingComponents (F ∩ annulus w r R) w r R).encard := by
  classical
  let S := crossingComponents (F ∩ ball w R) w r R
  let T := crossingComponents (F ∩ annulus w r R) w r R
  have hex : ∀ C ∈ S, ∃ D ∈ T, D ⊆ C := by
    intro C hC
    exact closed_ball_crossing_contains_annular_crossing_of_global_finite hF w hrR hC hfinite
  let pick : Set ℂ → Set ℂ := fun C => if hC : C ∈ S then
    Classical.choose (hex C hC) else ∅
  have hpick : ∀ C ∈ S, pick C ∈ T ∧ pick C ⊆ C := by
    intro C hC
    simpa [pick, hC] using Classical.choose_spec (hex C hC)
  apply Set.encard_le_encard_of_injOn (fun C hC => (hpick C hC).1)
  intro C hC D hD heq
  by_contra hne
  have hdisj := pairwiseDisjoint_connectedComponentsIn (F ∩ ball w R) hC.1 hD.1 hne
  obtain ⟨x, hx, hxD⟩ := (hpick C hC).1.1
  have hxpick : x ∈ pick C := by
    rw [← hxD]
    exact mem_connectedComponentIn hx
  exact Set.disjoint_left.mp hdisj ((hpick C hC).2 hxpick) ((hpick D hD).2 (heq ▸ hxpick))

end HarmonicBalls
