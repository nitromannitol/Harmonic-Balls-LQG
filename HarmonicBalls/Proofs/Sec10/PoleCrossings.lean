import HarmonicBalls.Proofs.Sec10.InteriorCrossingsExact

/-!
# Crossing bounds at the pole

For any fixed open cluster and any point in it, sufficiently small balls
are wholly contained in the cluster. This gives at most one crossing
component, including at the pole. The scale may depend on the mass.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- A preconnected set has at most one annular crossing component. -/
theorem IsPreconnected.encard_crossingComponents_le_one
    {F : Set ℂ} (hF : IsPreconnected F) (w : ℂ) (r R : ℝ) :
    (crossingComponents F w r R).encard ≤ 1 := by
  have hsub : crossingComponents F w r R ⊆ {F} := by
    intro C hC
    obtain ⟨x, hx, rfl⟩ := hC.1
    simpa only [mem_singleton_iff] using hF.connectedComponentIn hx
  exact (Set.encard_mono hsub).trans (by simp)

/-- For an open set, at every interior point and all sufficiently small
positive scales, the ball intersection has at most one crossing component. -/
theorem IsOpen.eventually_crossings_le_one_of_mem
    {G : Set ℂ} (hG : IsOpen G) {w : ℂ} (hw : w ∈ G) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ ρ ∈ Icc ε (Real.sqrt ε),
      (crossingComponents (G ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤ 1 := by
  obtain ⟨δ, hδ, hδG⟩ := Metric.isOpen_iff.mp hG w hw
  have hη : 0 < min (1 : ℝ) (δ / 4) := lt_min (by norm_num) (by positivity)
  filter_upwards [(eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hε hεpos
  change 0 < ε at hεpos
  have hε1 : ε < 1 := hε.trans_le (min_le_left _ _)
  have hεδ : ε < δ / 4 := hε.trans_le (min_le_right _ _)
  have hεsqrt : ε ≤ Real.sqrt ε := by
    have hs := Real.sq_sqrt hεpos.le
    have hn := Real.sqrt_nonneg ε
    nlinarith
  have hsub : ball w (2 * ε) ⊆ G :=
    (ball_subset_ball (by linarith : 2 * ε ≤ δ)).trans hδG
  refine ⟨ε, ⟨le_rfl, hεsqrt⟩, ?_⟩
  rw [inter_eq_right.mpr hsub]
  exact IsPreconnected.encard_crossingComponents_le_one
    (isConnected_ball (show 0 < 2 * ε by positivity)).isPreconnected w _ _

/-- For each fixed positive mass, the exact-radius crossing bound holds
at any nonzero interior point and at any point in the cluster. This includes
the pole even when it is the origin. The scale is not uniform in the mass. -/
theorem ae_interior_crossings_exact_radius_fixed_mass
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ w ∈ ball (0 : ℂ) 1,
      ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      (w ≠ 0 ∨ w ∈ cluster (μ ω) 1 z t) → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∃ ρ ∈ Icc ε (Real.sqrt ε),
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ := ae_interior_localized_crossings_exact_radius hI2 h6 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hbound hopen
  intro w hw z hz t ht hpoint
  by_cases hwG : w ∈ cluster (μ ω) 1 z t
  · have hω := IsOpen.eventually_crossings_le_one_of_mem
      (hopen t 1 ht zero_lt_one z hz).1 hwG
    filter_upwards [hω] with ε hε
    obtain ⟨ρ, hρ, hcount⟩ := hε
    refine ⟨ρ, hρ, hcount.trans ?_⟩
    exact_mod_cast (Nat.ceil_pos.mpr (one_div_pos.mpr hα.1))
  · have hw0 : w ≠ 0 := hpoint.resolve_right hwG
    have hzw : z ≠ w := by
      intro heq
      subst w
      exact hwG (self_mem_cluster hz)
    filter_upwards [hbound w hw hw0 z hz hzw] with ε hε
    obtain ⟨ρ, hρ, hρbound⟩ := hε
    exact ⟨ρ, hρ, hρbound t ht⟩

end HarmonicBalls
