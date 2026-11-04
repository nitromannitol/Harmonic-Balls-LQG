import HarmonicBalls.Proofs.Sec10.ComplementaryHoleCrossing
import HarmonicBalls.Proofs.Sec6.HarnackIteration

/-! # A whole annulus as a crossing in a complementary hole

A crossing component can be the entire annulus, with its closure disjoint
from both the set and the chosen complementary frontier. This is a
deterministic obstruction; it does not assert the existence of an LQG hole.
-/

namespace HarmonicBalls

open Set Metric Topology

/-- If a closed disk lies in an open region disjoint from `G` and `U`, the
only crossing component of `Uᶜ` in the concentric annulus is the whole
annulus. Its closure misses both `G` and the frontier of `U`. -/
theorem complementary_hole_crossing_is_whole_annulus
    {G U V : Set ℂ} (hGV : Disjoint G V) (hUV : Disjoint U V)
    (hV : IsOpen V) (w : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hball : closedBall w R ⊆ V) :
    crossingComponents (Uᶜ ∩ annulus w r R) w r R = {annulus w r R} ∧
      crossingComponents (G ∩ annulus w r R) w r R = ∅ ∧
      Disjoint G (closure (annulus w r R)) ∧
      Disjoint (closure (annulus w r R)) (frontier U) := by
  have hann : annulus w r R ⊆ closedBall w R := by
    intro x hx
    exact ball_subset_closedBall hx.1
  have hcl : closure (annulus w r R) ⊆ V :=
    (closure_minimal hann isClosed_closedBall).trans hball
  have heq : Uᶜ ∩ annulus w r R = annulus w r R := by
    ext x
    constructor
    · exact fun hx => hx.2
    · intro hx
      exact ⟨fun hxU => disjoint_left.mp hUV hxU (hcl (subset_closure hx)), hx⟩
  obtain ⟨⟨C, hC⟩, hGcross⟩ :=
    complementary_hole_has_crossing_without_set_crossing hGV hUV w hr hrR hball
  have hpre := Section6.isPreconnected_annulus w (le_of_lt hr) R
  have hCeq : C = annulus w r R := by
    rw [heq] at hC
    obtain ⟨x, hx, rfl⟩ := hC.1
    exact hpre.connectedComponentIn hx
  have hcross : crossingComponents (Uᶜ ∩ annulus w r R) w r R =
      {annulus w r R} := by
    apply Subset.antisymm
    · intro D hD
      rw [heq] at hD
      obtain ⟨x, hx, rfl⟩ := hD.1
      simpa only [mem_singleton_iff] using hpre.connectedComponentIn hx
    · rw [singleton_subset_iff]
      simpa [hCeq] using hC
  have hfrontdis : Disjoint (frontier U) V := by
    have hclU : closure U ⊆ Vᶜ :=
      closure_minimal (disjoint_left.mp hUV) hV.isClosed_compl
    exact disjoint_left.mpr (fun x hxU hxV => hclU (frontier_subset_closure hxU) hxV)
  exact ⟨hcross, hGcross, hGV.mono_right hcl, hfrontdis.symm.mono_left hcl⟩

/-- An open complementary hole meeting the unit disk contains an annulus
compactly contained in the disk for which the whole annulus is the crossing
component and its closure misses the chosen frontier. -/
theorem complementary_open_hole_has_whole_annulus_crossing
    {G U V : Set ℂ} (hGV : Disjoint G V) (hUV : Disjoint U V)
    (hV : IsOpen V) (hVdisk : (V ∩ ball (0 : ℂ) 1).Nonempty) :
    ∃ (w : ℂ) (r R : ℝ), 0 < r ∧ r < R ∧
      closure (annulus w r R) ⊆ ball 0 1 ∧
      crossingComponents (Uᶜ ∩ annulus w r R) w r R = {annulus w r R} ∧
      crossingComponents (G ∩ annulus w r R) w r R = ∅ ∧
      Disjoint G (closure (annulus w r R)) ∧
      Disjoint (closure (annulus w r R)) (frontier U) := by
  obtain ⟨w, hw⟩ := hVdisk
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp (hV.inter isOpen_ball) w hw
  have hball : closedBall w (ε / 2) ⊆ V ∩ ball (0 : ℂ) 1 :=
    (closedBall_subset_ball (by linarith)).trans hεsub
  have hr : 0 < ε / 4 := by positivity
  have hrR : ε / 4 < ε / 2 := by linarith
  have hann : annulus w (ε / 4) (ε / 2) ⊆ closedBall w (ε / 2) := by
    intro x hx
    exact ball_subset_closedBall hx.1
  have hcl : closure (annulus w (ε / 4) (ε / 2)) ⊆ ball (0 : ℂ) 1 :=
    (closure_minimal hann isClosed_closedBall).trans (hball.trans inter_subset_right)
  exact ⟨w, ε / 4, ε / 2, hr, hrR, hcl,
    complementary_hole_crossing_is_whole_annulus hGV hUV hV w hr hrR
      (hball.trans inter_subset_left)⟩

end HarmonicBalls
