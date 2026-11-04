import HarmonicBalls.Proofs.Sec10.DoubleEndpointSelection
import HarmonicBalls.Proofs.Sec10.ConnectedFrontierCrossings

/-!
# Boundary-free frontier obstruction

The exact-radius estimate also controls crossings near the pole whenever an
intermediate circle avoids the cluster frontier. Thus any excess crossing
forces the frontier itself to cross the annulus, without a fixed containment
margin.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- At the selected exact radius, either pole separation or an intermediate
circle avoiding the frontier suffices for the crossing bound. The scaling
inputs are staged pending source review. -/
theorem ae_boundary_free_crossings_of_frontier_gap_or_pole_margin
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ z : ℂ, ∀ t : ℝ, 0 < t →
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
        ((∃ s ∈ Ioo (ρ / 3) (2 * ρ),
          Disjoint (sphere w s) (frontier (cluster (μ ω) 1 z t))) ∨
          ρ + ρ / 50 < dist z w) →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ :=
    ae_crossings_without_boundary_margin_exact_all_poles hI2 h6 hAff hCC γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hbound hopen
  filter_upwards [hbound, (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hbound hε
  intro w hw
  obtain ⟨ρ, hρ, hρbound⟩ := hbound w hw
  have hρpos : 0 < ρ := hε.trans_le hρ.1
  refine ⟨ρ, hρ, ?_⟩
  intro z t ht hcl hcase
  rcases hcase with ⟨s, hs, hdis⟩ | hpole
  · by_cases hz : z ∈ ball (0 : ℂ) 1
    · apply (encard_crossingComponents_le_one_of_disjoint_intermediate_sphere_frontier
        (hopen t 1 ht zero_lt_one z hz).1 (by positivity) hs.1 hs.2 hdis).trans
      exact_mod_cast (Nat.ceil_pos.mpr (one_div_pos.mpr hα.1))
    · rw [cluster_eq_empty_of_pole_not_mem hz ht.le]
      simp [crossingComponents, connectedComponentsIn]
  · exact hρbound z t ht hcl hpole

/-- Excess crossings at the selected radius force a nearby pole and a
frontier crossing. If the frontier is connected, one of its annular
components crosses. -/
theorem ae_boundary_free_excess_crossings_force_frontier_crossing
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ z : ℂ, ∀ t : ℝ, 0 < t →
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
        (⌈1 / α⌉₊ : ℕ∞) <
          (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
            (2 * ρ)).encard →
        dist z w ≤ ρ + ρ / 50 ∧
        CrossesAnnulus (frontier (cluster (μ ω) 1 z t)) w (ρ / 3) (2 * ρ) ∧
        (∀ s ∈ Ioo (ρ / 3) (2 * ρ),
          (sphere w s ∩ frontier (cluster (μ ω) 1 z t)).Nonempty) ∧
        (IsConnected (frontier (cluster (μ ω) 1 z t)) →
          (crossingComponents (frontier (cluster (μ ω) 1 z t) ∩
            annulus w (ρ / 3) (2 * ρ)) w (ρ / 3) (2 * ρ)).Nonempty) := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ :=
    ae_boundary_free_crossings_of_frontier_gap_or_pole_margin hI2 h6 hAff hCC γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hbound hopen
  filter_upwards [hbound, (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hbound hε
  intro w hw
  obtain ⟨ρ, hρ, hρbound⟩ := hbound w hw
  have hρpos : 0 < ρ := hε.trans_le hρ.1
  refine ⟨ρ, hρ, ?_⟩
  intro z t ht hcl hexcess
  have hnear : dist z w ≤ ρ + ρ / 50 := by
    by_contra hn
    exact (not_le_of_gt hexcess) (hρbound z t ht hcl (Or.inr (lt_of_not_ge hn)))
  have hmeet : ∀ s ∈ Ioo (ρ / 3) (2 * ρ),
      (sphere w s ∩ frontier (cluster (μ ω) 1 z t)).Nonempty := by
    intro s hs
    by_contra hn
    have hdis : Disjoint (sphere w s) (frontier (cluster (μ ω) 1 z t)) :=
      disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn)
    exact (not_le_of_gt hexcess) (hρbound z t ht hcl (Or.inl ⟨s, hs, hdis⟩))
  have hz : z ∈ ball (0 : ℂ) 1 := by
    by_contra hn
    have hempty := cluster_eq_empty_of_pole_not_mem (μ := μ ω) hn ht.le
    simp [hempty, crossingComponents, connectedComponentsIn] at hexcess
  have hceil : (1 : ℕ∞) ≤ ⌈1 / α⌉₊ := by
    exact_mod_cast (Nat.ceil_pos.mpr (one_div_pos.mpr hα.1))
  have hfront := frontier_crosses_of_multiple_crossingComponents
    (w := w) (r := ρ / 3) (R := 2 * ρ)
    (hopen t 1 ht zero_lt_one z hz).1 (by positivity) (by linarith)
    (lt_of_le_of_lt hceil hexcess)
  refine ⟨hnear, hfront, hmeet, ?_⟩
  intro hconnected
  have hcompact : IsCompact (frontier (cluster (μ ω) 1 z t)) :=
    (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset isClosed_frontier
      (fun p hp => ball_subset_closedBall (hcl (frontier_subset_closure hp)))
  exact IsConnected.exists_annular_component_crossing_of_compact hconnected hcompact w
    (by linarith) hfront

end HarmonicBalls
