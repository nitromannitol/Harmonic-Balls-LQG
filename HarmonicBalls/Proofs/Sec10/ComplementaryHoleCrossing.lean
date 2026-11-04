import HarmonicBalls.Proofs.Sec10.IrreducibleTwoSidedConnected

/-!
# Annular crossings in complementary holes

An open region disjoint from both a set and a chosen complementary component
obstructs the crossing-containment assertion if it contains a suitable annulus.
This is a deterministic observation, not an existence assertion for LQG clusters.
-/

namespace HarmonicBalls

open Set Metric Topology

/-- An annulus in a region disjoint from `G` and `U` has a crossing component
of `Uᶜ`, but no crossing component of `G`. -/
theorem complementary_hole_has_crossing_without_set_crossing
    {G U V : Set ℂ} (hGV : Disjoint G V) (hUV : Disjoint U V)
    (w : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hball : closedBall w R ⊆ V) :
    (crossingComponents (Uᶜ ∩ annulus w r R) w r R).Nonempty ∧
      crossingComponents (G ∩ annulus w r R) w r R = ∅ := by
  have hR : 0 ≤ R := le_of_lt (lt_trans hr hrR)
  have hannball : annulus w r R ⊆ closedBall w R := by
    intro x hx
    exact ball_subset_closedBall hx.1
  have hannV : annulus w r R ⊆ V := hannball.trans hball
  have hUann : Uᶜ ∩ annulus w r R = closedBall w R ∩ annulus w r R := by
    ext x
    constructor
    · rintro ⟨_, hx⟩
      exact ⟨hannball hx, hx⟩
    · rintro ⟨_, hx⟩
      exact ⟨fun hxU => Set.disjoint_left.mp hUV hxU (hannV hx), hx⟩
  have hcross : CrossesAnnulus (closedBall w R) w r R := by
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := w) (r := r)).2 (le_of_lt hr)
    obtain ⟨y, hy⟩ := (NormedSpace.sphere_nonempty (x := w) (r := R)).2 hR
    constructor
    · exact ⟨x, subset_closure (mem_closedBall.mpr (le_of_lt (by
        rw [mem_sphere.mp hx]; exact hrR))), hx⟩
    · exact ⟨y, subset_closure (sphere_subset_closedBall hy), hy⟩
  constructor
  · rw [hUann]
    exact IsConnected.exists_annular_component_crossing (isConnected_closedBall (x := w) hR)
      (isCompact_closedBall w R) w hrR Subset.rfl hcross
  · have hempty : G ∩ annulus w r R = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
      rintro ⟨hxG, hxA⟩
      exact Set.disjoint_left.mp hGV hxG (hannV hxA)
    rw [hempty]
    simp [crossingComponents, connectedComponentsIn]

/-- Every open region inside the unit disk disjoint from both `G` and `U`
contains an annulus witnessing failure of crossing containment. -/
theorem complementary_open_hole_obstructs_crossing_containment
    {G U V : Set ℂ} (hGV : Disjoint G V) (hUV : Disjoint U V)
    (hV : IsOpen V) (hVdisk : (V ∩ ball (0 : ℂ) 1).Nonempty) :
    ∃ (w : ℂ) (r R : ℝ), 0 < r ∧ r < R ∧
      closure (annulus w r R) ⊆ ball 0 1 ∧
      ∃ C ∈ crossingComponents (Uᶜ ∩ annulus w r R) w r R,
        ¬ ∃ C' ∈ crossingComponents (G ∩ annulus w r R) w r R, C' ⊆ C := by
  obtain ⟨w, hw⟩ := hVdisk
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp (hV.inter isOpen_ball) w hw
  have hR : ε / 2 < ε := by linarith
  have hball : closedBall w (ε / 2) ⊆ V ∩ ball (0 : ℂ) 1 :=
    (closedBall_subset_ball hR).trans hεsub
  have hann : annulus w (ε / 4) (ε / 2) ⊆ closedBall w (ε / 2) := by
    intro x hx
    exact ball_subset_closedBall hx.1
  have hr : 0 < ε / 4 := by positivity
  have hrR : ε / 4 < ε / 2 := by linarith
  have hcl : closure (annulus w (ε / 4) (ε / 2)) ⊆ ball (0 : ℂ) 1 :=
    (closure_minimal hann isClosed_closedBall).trans (hball.trans inter_subset_right)
  obtain ⟨⟨C, hC⟩, hnone⟩ :=
    complementary_hole_has_crossing_without_set_crossing hGV hUV w hr hrR
      (hball.trans inter_subset_left)
  refine ⟨w, ε / 4, ε / 2, hr, hrR, hcl, C, hC, ?_⟩
  rintro ⟨C', hC', _⟩
  rw [hnone] at hC'
  exact hC'

/-- The crossing-containment conclusion rules out any open region in the
unit disk disjoint from both the set and the chosen component. -/
theorem crossing_containment_forbids_complementary_open_hole
    {G U V : Set ℂ} (hGV : Disjoint G V) (hUV : Disjoint U V)
    (hV : IsOpen V)
    (hcontain : ∀ (w : ℂ) (r R : ℝ), 0 < r → r < R →
      closure (annulus w r R) ⊆ ball 0 1 →
      ∀ C ∈ crossingComponents (Uᶜ ∩ annulus w r R) w r R,
        ∃ C' ∈ crossingComponents (G ∩ annulus w r R) w r R, C' ⊆ C) :
    ¬ (V ∩ ball (0 : ℂ) 1).Nonempty := by
  intro hnon
  obtain ⟨w, r, R, hr, hrR, hcl, C, hC, hnone⟩ :=
    complementary_open_hole_obstructs_crossing_containment hGV hUV hV hnon
  exact hnone (hcontain w r R hr hrR hcl C hC)

end HarmonicBalls
