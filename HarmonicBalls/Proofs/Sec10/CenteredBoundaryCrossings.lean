import HarmonicBalls.Proofs.Sec10.BoundaryCrossings

/-!
# Crossing bounds for clusters centred at the origin

For these clusters, the origin belongs to the open cluster and cannot lie on
a complementary boundary. The boundary-point crossing estimate therefore
applies at every point of every complementary boundary.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- If the origin belongs to the cluster, the nonzero restriction on boundary
points is automatic. The boundary-bumping hypothesis remains explicit. -/
theorem ae_boundary_complement_localized_crossings_of_origin_mem
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      (0 : ℂ) ∈ cluster (μ ω) 1 z t →
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      ∀ w ∈ frontier U, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∃ ρ ∈ Icc ε (Real.sqrt ε),
        (∀ C ∈ crossingComponents (Uᶜ ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ),
          ∃ D ∈ crossingComponents (Uᶜ ∩ annulus w (ρ / 3) (2 * ρ))
            w (ρ / 3) (2 * ρ), D ⊆ C) →
        (crossingComponents (Uᶜ ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ := ae_boundary_complement_localized_crossings hI2 h6 h5 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ,
    clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα₀ hC hcirc μ hGFF hμ hI2,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hbound hgeom hopen
  intro t ht z hz h0mem hcl U hU w hw
  have hfront := (hgeom t 1 ht zero_lt_one z hz hcl U hU).2.2.2.1 hw
  have hw0 : w ≠ 0 := by
    intro h
    subst w
    rw [(hopen t 1 ht zero_lt_one z hz).1.frontier_eq] at hfront
    exact hfront.2 h0mem
  exact hbound t ht z hz hcl U hU w hw hw0

/-- In particular, this applies at every complementary boundary point for
clusters centred at the origin. -/
theorem ae_centered_boundary_complement_localized_crossings
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
      closure (cluster (μ ω) 1 0 t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 0 t))ᶜ,
      ∀ w ∈ frontier U, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∃ ρ ∈ Icc ε (Real.sqrt ε),
        (∀ C ∈ crossingComponents (Uᶜ ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ),
          ∃ D ∈ crossingComponents (Uᶜ ∩ annulus w (ρ / 3) (2 * ρ))
            w (ρ / 3) (2 * ρ), D ⊆ C) →
        (crossingComponents (Uᶜ ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ :=
    ae_boundary_complement_localized_crossings_of_origin_mem hI2 h6 h5 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ] with ω hω
  intro t ht hcl U hU w hw
  have h0 : (0 : ℂ) ∈ ball 0 1 := by simp
  exact hω t ht 0 h0 (self_mem_cluster h0) hcl U hU w hw

end HarmonicBalls
