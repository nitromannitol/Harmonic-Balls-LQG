import HarmonicBalls.Proofs.Sec10.PoleCrossings
import HarmonicBalls.Proofs.Sec3.Basic

/-!
# Crossing bounds above a positive mass

A point inside one cluster stays inside every later cluster. Thus its
neighborhood supplies a crossing bound uniformly over all later masses.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Around a point of an open set, one radius works for every superset of
that set and gives at most one crossing component. -/
theorem IsOpen.eventually_crossings_le_one_of_subset
    {G : Set ℂ} (hG : IsOpen G) {w : ℂ} (hw : w ∈ G) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ ρ ∈ Icc ε (Real.sqrt ε),
      ∀ H : Set ℂ, G ⊆ H →
        (crossingComponents (H ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤ 1 := by
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
  intro H hGH
  rw [inter_eq_right.mpr (hsub.trans hGH)]
  exact IsPreconnected.encard_crossingComponents_le_one
    (isConnected_ball (show 0 < 2 * ε by positivity)).isPreconnected w _ _

/-- Uniformly for masses above any fixed positive lower bound, the
exact-radius crossing estimate holds at each fixed nonzero interior point,
and at the origin whenever it belongs to the cluster at the lower mass.
In particular, the pole is allowed even when it is the origin. -/
theorem ae_interior_crossings_exact_radius_above_mass
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ w ∈ ball (0 : ℂ) 1,
      ∀ z ∈ ball (0 : ℂ) 1, ∀ t₀ : ℝ, 0 < t₀ →
      (w ≠ 0 ∨ w ∈ cluster (μ ω) 1 z t₀) → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ t : ℝ, t₀ ≤ t →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ := ae_interior_localized_crossings_exact_radius hI2 h6 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hbound hopen hmono
  intro w hw z hz t₀ ht₀ hpoint
  by_cases hwG : w ∈ cluster (μ ω) 1 z t₀
  · have hω := IsOpen.eventually_crossings_le_one_of_subset
      (hopen t₀ 1 ht₀ zero_lt_one z hz).1 hwG
    filter_upwards [hω] with ε hε
    obtain ⟨ρ, hρ, hcount⟩ := hε
    refine ⟨ρ, hρ, ?_⟩
    intro t htt
    exact (hcount (cluster (μ ω) 1 z t) (hmono t₀ t 1 ht₀ htt zero_lt_one z hz)).trans
      (by exact_mod_cast (Nat.ceil_pos.mpr (one_div_pos.mpr hα.1)))
  · have hw0 : w ≠ 0 := hpoint.resolve_right hwG
    have hzw : z ≠ w := by
      intro heq
      subst w
      exact hwG (self_mem_cluster hz)
    filter_upwards [hbound w hw hw0 z hz hzw] with ε hε
    obtain ⟨ρ, hρ, hρbound⟩ := hε
    exact ⟨ρ, hρ, fun t htt => hρbound t (ht₀.trans_le htt)⟩

/-- Above any fixed positive lower mass, crossings centered at the pole are
uniformly bounded by one, including at the origin. Only volume growth is
needed; the radius threshold can depend on the pole and lower mass. -/
theorem ae_pole_crossings_le_one_above_mass
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t₀ : ℝ, 0 < t₀ →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ t : ℝ, t₀ ≤ t →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball z (2 * ρ)) z (ρ / 3)
          (2 * ρ)).encard ≤ 1 := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hopen hmono
  intro z hz t₀ ht₀
  have hω := IsOpen.eventually_crossings_le_one_of_subset
    (hopen t₀ 1 ht₀ zero_lt_one z hz).1 (self_mem_cluster hz)
  filter_upwards [hω] with ε hε
  obtain ⟨ρ, hρ, hcount⟩ := hε
  exact ⟨ρ, hρ, fun t htt => hcount (cluster (μ ω) 1 z t)
    (hmono t₀ t 1 ht₀ htt zero_lt_one z hz)⟩

end HarmonicBalls
