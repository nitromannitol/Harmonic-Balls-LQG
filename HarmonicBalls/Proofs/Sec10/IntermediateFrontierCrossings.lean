import HarmonicBalls.Proofs.Sec10.CrossingIntermediateCircle
import HarmonicBalls.Proofs.Sec10.FrontierCrossingObstruction

/-!
# Frontier contacts at intermediate radii

A crossing meets every intermediate circle. If one of these circles avoids
the frontier, it controls all crossings just as the inner circle does.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Moving the inner radius outward preserves each crossing component when
the new radius is strictly between the original radii. -/
theorem crossingComponents_mono_inner_radius
    (F : Set ℂ) (w : ℂ) {r s R : ℝ} (hrs : r < s) (hsR : s < R) :
    crossingComponents F w r R ⊆ crossingComponents F w s R := by
  intro C hC
  obtain ⟨x, hx, hxeq⟩ := hC.1
  have hpre : IsPreconnected C := by
    rw [← hxeq]
    exact isPreconnected_connectedComponentIn
  obtain ⟨p, hpC, hps⟩ := IsPreconnected.exists_mem_sphere_of_crosses hpre hrs hsR hC.2
  exact ⟨hC.1, ⟨⟨p, subset_closure hpC, hps⟩, hC.2.2⟩⟩

/-- An intermediate circle disjoint from the frontier of an open set forces
at most one crossing component. -/
theorem encard_crossingComponents_le_one_of_disjoint_intermediate_sphere_frontier
    {G : Set ℂ} (hG : IsOpen G) {w : ℂ} {r s R : ℝ} (hr : 0 ≤ r)
    (hrs : r < s) (hsR : s < R) (hdis : Disjoint (sphere w s) (frontier G)) :
    (crossingComponents (G ∩ ball w R) w r R).encard ≤ 1 := by
  apply (Set.encard_mono (crossingComponents_mono_inner_radius (G ∩ ball w R) w hrs hsR)).trans
  exact encard_crossingComponents_le_one_of_disjoint_inner_sphere_frontier hG
    (le_of_lt (lt_of_le_of_lt hr hrs)) hsR hdis

/-- If an open set has more than one crossing component, its frontier
crosses the same annulus. -/
theorem frontier_crosses_of_multiple_crossingComponents
    {G : Set ℂ} (hG : IsOpen G) {w : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hcount : 1 < (crossingComponents (G ∩ ball w R) w r R).encard) :
    CrossesAnnulus (frontier G) w r R := by
  let K : Set ℂ := frontier G ∩ closedBall w (R + 1)
  have hK : IsCompact K := (isCompact_closedBall w (R + 1)).of_isClosed_subset
    (isClosed_frontier.inter isClosed_closedBall) inter_subset_right
  let f : ℂ → ℝ := fun p => dist p w
  have hf : Continuous f := continuous_id.dist continuous_const
  have himage : IsClosed (f '' K) := (hK.image hf).isClosed
  have hinterior : Ioo r R ⊆ f '' K := by
    intro s hs
    have hmeet : (sphere w s ∩ frontier G).Nonempty := by
      by_contra hn
      have hdis : Disjoint (sphere w s) (frontier G) :=
        disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn)
      exact (not_le_of_gt hcount)
        (encard_crossingComponents_le_one_of_disjoint_intermediate_sphere_frontier
          hG hr hs.1 hs.2 hdis)
    obtain ⟨p, hps, hpG⟩ := hmeet
    have hpK : p ∈ K := ⟨hpG, mem_closedBall.mpr (by rw [mem_sphere.mp hps]; linarith [hs.2])⟩
    exact ⟨p, hpK, mem_sphere.mp hps⟩
  have hclosed : Icc r R ⊆ f '' K := by
    rw [← closure_Ioo (ne_of_lt hrR)]
    exact closure_minimal hinterior himage
  obtain ⟨a, ha, har⟩ := hclosed ⟨le_rfl, hrR.le⟩
  obtain ⟨b, hb, hbR⟩ := hclosed ⟨hrR.le, le_rfl⟩
  exact ⟨⟨a, subset_closure ha.1, mem_sphere.mpr har⟩,
    ⟨b, subset_closure hb.1, mem_sphere.mpr hbR⟩⟩

/-- With a fixed containment margin, excess crossings force a nearby pole
and a frontier crossing, including contact with every intermediate circle. -/
theorem ae_excess_contained_crossings_meet_every_intermediate_sphere
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ b : ℝ, b < 1 → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 b →
        (⌈1 / α⌉₊ : ℕ∞) <
          (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
            (2 * ρ)).encard →
        ‖w‖ ≤ (b + 1) / 2 ∧ dist z w ≤ ρ + ρ / 50 ∧
          CrossesAnnulus (frontier (cluster (μ ω) 1 z t)) w (ρ / 3) (2 * ρ) ∧
          ∀ s ∈ Ioo (ρ / 3) (2 * ρ),
            (sphere w s ∩ frontier (cluster (μ ω) 1 z t)).Nonempty := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ :=
    ae_excess_contained_crossings_meet_frontier_near_pole hI2 h6 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hbound hopen
  intro b hb
  filter_upwards [hbound b hb,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hbound hε
  intro w hw
  obtain ⟨ρ, hρ, hρbound⟩ := hbound w hw
  have hρpos : 0 < ρ := hε.trans_le hρ.1
  refine ⟨ρ, hρ, ?_⟩
  intro z hz t ht hcl hexcess
  obtain ⟨hwnear, hznear, _⟩ := hρbound z hz t ht hcl hexcess
  have hceil : (1 : ℕ∞) ≤ ⌈1 / α⌉₊ := by
    exact_mod_cast (Nat.ceil_pos.mpr (one_div_pos.mpr hα.1))
  have hfront := frontier_crosses_of_multiple_crossingComponents
    (w := w) (r := ρ / 3) (R := 2 * ρ)
    (hopen t 1 ht zero_lt_one z hz).1 (by positivity) (by linarith)
    (lt_of_le_of_lt hceil hexcess)
  refine ⟨hwnear, hznear, hfront, ?_⟩
  intro s hs
  by_contra hnonempty
  have hdis : Disjoint (sphere w s) (frontier (cluster (μ ω) 1 z t)) :=
    disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hnonempty)
  have hone := encard_crossingComponents_le_one_of_disjoint_intermediate_sphere_frontier
    (w := w) (r := ρ / 3) (s := s) (R := 2 * ρ)
    (hopen t 1 ht zero_lt_one z hz).1 (by positivity) hs.1 hs.2 hdis
  exact (not_le_of_gt hexcess) (hone.trans hceil)

end HarmonicBalls
