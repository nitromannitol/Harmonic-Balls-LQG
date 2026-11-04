import HarmonicBalls.Proofs.Sec10.BoundaryCentersContained
import HarmonicBalls.Proofs.Sec10.CompactPoleConfinement

/-!
# Crossing bounds outside an intermediate mass interval

Small-mass confinement holds at every sufficiently large crossing radius,
so it can be combined with the radius chosen for masses above a fixed
positive threshold.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- For clusters in a fixed subdisc, one radius controls all masses outside
an intermediate interval. The lower endpoint depends on the scale. -/
theorem ae_contained_crossings_outside_intermediate_masses
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (hvolume : LiouvilleVolumeGrowthStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ b t₀ : ℝ, b < 1 → 0 < t₀ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∃ T : ℝ, 0 < T ∧ ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ z : ℂ, ∀ t : ℝ, 0 < t →
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 b → (t ≤ T ∨ t₀ ≤ t) →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ := ae_contained_cluster_crossings_above_mass hI2 h6 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_compact_poles_small_mass_crossings hvolume (clusterOpenLaplacian_proved hI2)
      (clusterConservationOfMass_proved hI2) (harnackTypeEstimateStmt_of_component h6)
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω habove hsmall
  intro b t₀ hb ht₀
  filter_upwards [habove b t₀ hb ht₀,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε habove hε
  obtain ⟨T, hT, hsmall⟩ := hsmall b ε hb hε
  refine ⟨T, hT, ?_⟩
  intro w hw
  obtain ⟨ρ, hρ, hρbound⟩ := habove w hw
  refine ⟨ρ, hρ, ?_⟩
  intro z t ht hcl hmass
  rcases hmass with htT | htt₀
  · by_cases hz : z ∈ ball (0 : ℂ) 1
    · have hzb : z ∈ ball (0 : ℂ) b := hcl (subset_closure (self_mem_cluster hz))
      rw [hsmall t ⟨ht, htT⟩ z hzb w ρ hρ.1]
      simp
    · rw [cluster_eq_empty_of_pole_not_mem hz ht.le]
      simp [crossingComponents, connectedComponentsIn]
  · exact hρbound z t htt₀ hcl

end HarmonicBalls
