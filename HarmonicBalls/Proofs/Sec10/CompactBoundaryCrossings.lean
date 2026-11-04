import HarmonicBalls.Proofs.Sec10.ClosedCrossingContinuum
import HarmonicBalls.Proofs.Sec10.CenteredBoundaryCrossings

/-!
# Complementary crossings from compact-continuum boundary bumping

The remaining topological premise is stated for compact connected sets. These
lemmas apply the reduction to complementary components, which are open, and
therefore have closed complements. The compact-continuum premise is not proved
here.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- The compact-continuum crossing premise implies the complementary crossing
count comparison at all admissible centres and scales. -/
theorem ae_clusterComplement_crossings_le_of_compact_continuum
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u})
    (hcompactBump : ∀ (w : ℂ) (r R : ℝ), 0 < r → r < R →
      ∀ K : Set ℂ, IsCompact K → IsConnected K → K ⊆ closedBall w R →
        CrossesAnnulus K w r R →
        (crossingComponents (K ∩ annulus w r R) w r R).Nonempty)
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (w : ℂ) (r R : ℝ), 0 < r → r < R →
      closure (annulus w r R) ⊆ ball 0 1 →
      ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      (crossingComponents (Uᶜ ∩ ball w R) w r R).encard ≤
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w R) w r R).encard := by
  filter_upwards [ae_clusterComplement_crossings_le hI2 h5 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2] with ω hbound hgeom
  intro w r R hr hrR hann t ht z hz hcl U hU
  have hUopen := (hgeom t 1 ht zero_lt_one z hz hcl U hU).1
  apply hbound w r R hr hrR hann t ht z hz hcl U hU
  intro C hC'
  exact closed_ball_crossing_contains_annular_crossing_of_compact_continuum
    hUopen.isClosed_compl w hrR (hcompactBump w r R hr hrR) hC'

/-- With the same compact-continuum premise, the complementary crossing
bound holds at every nonzero complementary boundary point. -/
theorem ae_boundary_complement_localized_crossings_of_compact_continuum
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u})
    (hcompactBump : ∀ (w : ℂ) (r R : ℝ), 0 < r → r < R →
      ∀ K : Set ℂ, IsCompact K → IsConnected K → K ⊆ closedBall w R →
        CrossesAnnulus K w r R →
        (crossingComponents (K ∩ annulus w r R) w r R).Nonempty) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      ∀ w ∈ frontier U, w ≠ 0 → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∃ ρ ∈ Icc ε (Real.sqrt ε),
        (crossingComponents (Uᶜ ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ := ae_boundary_complement_localized_crossings hI2 h6 h5 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ,
    clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα₀
      hC hcirc μ hGFF hμ hI2] with ω hbound hgeom
  intro t ht z hz hcl U hU w hw hw0
  have hUopen := (hgeom t 1 ht zero_lt_one z hz hcl U hU).1
  filter_upwards [hbound t ht z hz hcl U hU w hw hw0,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hε hεpos
  obtain ⟨ρ, hρ, hcount⟩ := hε
  have hρpos : 0 < ρ := hεpos.trans_le hρ.1
  have hr : 0 < ρ / 3 := by linarith
  have hrR : ρ / 3 < 2 * ρ := by linarith
  refine ⟨ρ, hρ, hcount ?_⟩
  intro C hC'
  exact closed_ball_crossing_contains_annular_crossing_of_compact_continuum
    hUopen.isClosed_compl w hrR (hcompactBump w (ρ / 3) (2 * ρ) hr hrR) hC'

/-- For clusters centred at the origin, the estimate applies at every point
of every complementary boundary. -/
theorem ae_centered_boundary_complement_localized_crossings_of_compact_continuum
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u})
    (hcompactBump : ∀ (w : ℂ) (r R : ℝ), 0 < r → r < R →
      ∀ K : Set ℂ, IsCompact K → IsConnected K → K ⊆ closedBall w R →
        CrossesAnnulus K w r R →
        (crossingComponents (K ∩ annulus w r R) w r R).Nonempty) :
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
        (crossingComponents (Uᶜ ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ :=
    ae_boundary_complement_localized_crossings_of_compact_continuum hI2 h6 h5 hcompactBump γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ,
    clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα₀
      hC hcirc μ hGFF hμ hI2,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hbound hgeom hopen
  intro t ht hcl U hU w hw
  have h0 : (0 : ℂ) ∈ ball 0 1 := by simp
  have hfront := (hgeom t 1 ht zero_lt_one 0 h0 hcl U hU).2.2.2.1 hw
  have hw0 : w ≠ 0 := by
    intro h
    subst w
    rw [(hopen t 1 ht zero_lt_one 0 h0).1.frontier_eq] at hfront
    exact hfront.2 (self_mem_cluster h0)
  exact hbound t ht 0 h0 hcl U hU w hw hw0

end HarmonicBalls
