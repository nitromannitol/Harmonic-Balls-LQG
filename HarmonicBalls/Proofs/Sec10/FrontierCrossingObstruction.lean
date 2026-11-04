import HarmonicBalls.Proofs.Sec10.ContainedInnerBallCrossings
import HarmonicBalls.Proofs.Sec5.NoEntryTopology

/-!
# Frontier obstruction to excess crossing components

A connected inner circle which does not meet the frontier of an open set
lies either inside or outside the set. In either case there is at most one
crossing component.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- If the inner circle avoids the frontier, there is at most one crossing
component. -/
theorem encard_crossingComponents_le_one_of_disjoint_inner_sphere_frontier
    {G : Set ℂ} (hG : IsOpen G) {w : ℂ} {r R : ℝ} (hr : 0 ≤ r)
    (hrR : r < R) (hdis : Disjoint (sphere w r) (frontier G)) :
    (crossingComponents (G ∩ ball w R) w r R).encard ≤ 1 := by
  have hs := (isConnected_sphere (by simp) w hr).isPreconnected
  rcases IsPreconnected.subset_or_disjoint_of_disjoint_frontier hs hG hdis with hsub | hdisG
  · exact encard_crossingComponents_le_one_of_inner_sphere hG hr hrR hsub
  · have hempty : crossingComponents (G ∩ ball w R) w r R = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro C hC
      obtain ⟨p, hpcl, hps⟩ := hC.2.1
      obtain ⟨x, hx, rfl⟩ := hC.1
      have hpGcl : p ∈ closure G :=
        closure_mono ((connectedComponentIn_subset (G ∩ ball w R) x).trans inter_subset_left) hpcl
      have hpG : p ∉ G := fun hp => disjoint_left.mp hdisG hps hp
      have hpf : p ∈ frontier G := by
        rw [hG.frontier_eq]
        exact ⟨hpGcl, hpG⟩
      exact disjoint_left.mp hdis hps hpf
    rw [hempty]
    simp

/-- For contained clusters, failure of the uniform crossing bound forces the
pole to be near the crossing center and the inner circle to meet the cluster
frontier. -/
theorem ae_excess_contained_crossings_meet_frontier_near_pole
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
          (sphere w (ρ / 3) ∩ frontier (cluster (μ ω) 1 z t)).Nonempty := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ := ae_contained_crossings_with_pole_margin hI2 h6 γ hγ hγ2
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
  have hmargin : ¬ (‖w‖ ≤ (b + 1) / 2 → ρ + ρ / 50 < dist z w) := by
    intro h
    exact (not_le_of_gt hexcess) (hρbound z hz t ht hcl h)
  have hnear : ‖w‖ ≤ (b + 1) / 2 ∧ dist z w ≤ ρ + ρ / 50 := by
    push Not at hmargin
    exact hmargin
  refine ⟨hnear.1, hnear.2, ?_⟩
  by_contra hnonempty
  have hdis : Disjoint (sphere w (ρ / 3)) (frontier (cluster (μ ω) 1 z t)) :=
    disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hnonempty)
  have hone := encard_crossingComponents_le_one_of_disjoint_inner_sphere_frontier
    (w := w) (r := ρ / 3) (R := 2 * ρ) (hopen t 1 ht zero_lt_one z hz).1 (by positivity) (by linarith) hdis
  have hceil : (1 : ℕ∞) ≤ ⌈1 / α⌉₊ := by
    exact_mod_cast (Nat.ceil_pos.mpr (one_div_pos.mpr hα.1))
  exact (not_le_of_gt hexcess) (hone.trans hceil)

end HarmonicBalls
