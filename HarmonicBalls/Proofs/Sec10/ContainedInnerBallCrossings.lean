import HarmonicBalls.Proofs.Sec10.ContainedSharpCrossings
import HarmonicBalls.Proofs.Sec10.ComplementComponents

/-!
# Crossing bounds when the inner disk is contained

An open set containing the inner circle has at most one crossing component. This supplements the pole-separated localization estimate.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- If an open set contains the inner circle, every crossing component
meets that circle and hence belongs to the same component. -/
theorem encard_crossingComponents_le_one_of_inner_sphere
    {G : Set ℂ} (hG : IsOpen G) {w : ℂ} {r R : ℝ} (hr : 0 ≤ r)
    (hrR : r < R) (hsphere : sphere w r ⊆ G) :
    (crossingComponents (G ∩ ball w R) w r R).encard ≤ 1 := by
  let F := G ∩ ball w R
  have hF : IsOpen F := hG.inter isOpen_ball
  have hsphereF : sphere w r ⊆ F :=
    fun x hx => ⟨hsphere hx, closedBall_subset_ball hrR (sphere_subset_closedBall hx)⟩
  obtain ⟨q, hq⟩ := (isConnected_sphere (by simp) w hr).nonempty
  have hspherecomp : sphere w r ⊆ connectedComponentIn F q :=
    (isConnected_sphere (by simp) w hr).isPreconnected.subset_connectedComponentIn hq hsphereF
  have hsub : crossingComponents F w r R ⊆ {connectedComponentIn F q} := by
    intro C hC
    obtain ⟨p, hpC, hps⟩ := hC.2.1
    obtain ⟨x, hx, rfl⟩ := hC.1
    have hpcomp : p ∈ connectedComponentIn F x :=
      mem_connectedComponentIn_of_mem_closure hF (hsphereF hps) hpC
    simpa only [mem_singleton_iff] using
      (connectedComponentIn_eq hpcomp).trans (connectedComponentIn_eq (hspherecomp hps)).symm
  exact (Set.encard_mono hsub).trans (by simp)

/-- The closed-disk version of the inner-circle crossing bound. -/
theorem encard_crossingComponents_le_one_of_closed_inner_ball
    {G : Set ℂ} (hG : IsOpen G) {w : ℂ} {r R : ℝ} (hr : 0 ≤ r)
    (hrR : r < R) (hball : closedBall w r ⊆ G) :
    (crossingComponents (G ∩ ball w R) w r R).encard ≤ 1 :=
  encard_crossingComponents_le_one_of_inner_sphere hG hr hrR
    (sphere_subset_closedBall.trans hball)

/-- For contained clusters, the uniform crossing bound holds either when the
inner circle is contained in the cluster or under the pole margin from
localization. The chosen radius is uniform over all positive masses. -/
theorem ae_contained_crossings_with_inner_sphere_or_pole_margin
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
        (sphere w (ρ / 3) ⊆ cluster (μ ω) 1 z t ∨
          (‖w‖ ≤ (b + 1) / 2 → ρ + ρ / 50 < dist z w)) →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
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
  intro z hz t ht hcl hcase
  rcases hcase with hball | hpole
  · apply (encard_crossingComponents_le_one_of_inner_sphere
      (hopen t 1 ht zero_lt_one z hz).1 (by positivity) (by linarith) hball).trans
    exact_mod_cast (Nat.ceil_pos.mpr (one_div_pos.mpr hα.1))
  · exact hρbound z hz t ht hcl hpole

end HarmonicBalls
