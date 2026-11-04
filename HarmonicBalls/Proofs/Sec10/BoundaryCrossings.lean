import HarmonicBalls.Proofs.Sec10.CrossingTransfer
import HarmonicBalls.Proofs.Sec10.InteriorCrossingsExact

/-!
# Crossing bounds at complementary boundary points

The localized crossing estimate applies at each nonzero boundary point: the
cluster is open, contains its pole, and is compactly contained in the disc.
The boundary-bumping hypothesis remains explicit in the complementary count.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- At every nonzero complementary boundary point, sufficiently small scales
admit a radius for which boundary bumping and Lemma 10.5 bound the number of
complementary crossings. The bound is deterministic and depends only on γ. -/
theorem ae_boundary_complement_localized_crossings
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
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
        (∀ C ∈ crossingComponents (Uᶜ ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ),
          ∃ D ∈ crossingComponents (Uᶜ ∩ annulus w (ρ / 3) (2 * ρ))
            w (ρ / 3) (2 * ρ), D ⊆ C) →
        (crossingComponents (Uᶜ ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hcross⟩ := ae_interior_localized_crossings_exact_radius hI2 h6 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hcross α₀ hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_clusterComplement_crossings_le hI2 h5 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα₀ hC hcirc μ hGFF hμ hI2,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hbound htransfer hgeom hopen
  intro t ht z hz hcl U hU w hw hw0
  have hg := hgeom t 1 ht zero_lt_one z hz hcl U hU
  have hwfront : w ∈ frontier (cluster (μ ω) 1 z t) := hg.2.2.2.1 hw
  have hwball : w ∈ ball (0 : ℂ) 1 := hcl (frontier_subset_closure hwfront)
  have hGopen := (hopen t 1 ht zero_lt_one z hz).1
  have hzw : z ≠ w := by
    intro h
    subst w
    have hzG := self_mem_cluster (μ := μ ω) (t := t) hz
    rw [hGopen.frontier_eq] at hwfront
    exact hwfront.2 hzG
  have hwunit : dist w 0 < 1 := mem_ball.mp hwball
  let η : ℝ := (1 - dist w 0) / 4
  have hη : 0 < η := by dsimp [η]; linarith
  filter_upwards [hbound w hwball hw0 z hz hzw,
    (eventually_lt_nhds (sq_pos_of_pos hη)).filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hε hsmall hεpos
  have hsqrt : Real.sqrt ε < η := by
    have hs := Real.sqrt_lt_sqrt hεpos.le hsmall
    simpa [Real.sqrt_sq_eq_abs, abs_of_pos hη] using hs
  obtain ⟨ρ, hρ, hρbound⟩ := hε
  have hρpos : 0 < ρ := hεpos.trans_le hρ.1
  have hρunit : dist w 0 + 2 * ρ < 1 := by dsimp [η] at hsqrt; linarith [hρ.2]
  have hann : closure (annulus w (ρ / 3) (2 * ρ)) ⊆ ball (0 : ℂ) 1 := by
    intro x hx
    have hxcl : x ∈ closedBall w (2 * ρ) :=
      closure_ball_subset_closedBall (closure_mono (show annulus w (ρ / 3) (2 * ρ) ⊆
        ball w (2 * ρ) from sdiff_subset) hx)
    apply mem_ball.mpr
    have hxw := mem_closedBall.mp hxcl
    have htri := dist_triangle x w (0 : ℂ)
    linarith
  refine ⟨ρ, hρ, ?_⟩
  intro hbump
  have hcount := htransfer w (ρ / 3) (2 * ρ) (by linarith) (by linarith) hann
    t ht z hz hcl U hU hbump
  exact hcount.trans (hρbound t ht)

end HarmonicBalls
