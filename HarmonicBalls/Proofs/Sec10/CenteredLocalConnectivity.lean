import HarmonicBalls.Proofs.Sec10.ClosedContinuumBoundaryBumping
import HarmonicBalls.Proofs.Sec10.CompactBoundaryCrossings

/-!
# Local connectivity of centered cluster complements

The remaining geometric inputs are Lemma 10.5 and the two-circle crossing
property for compact continua, both kept explicit below.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- The complement of every complementary component of a centered cluster is
locally connected, conditional on the annular crossing inputs. -/
theorem ae_centered_complement_locallyConnected_of_compact_continuum
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u})
    (hcompactBump : ∀ (w : ℂ) (r R : ℝ), 0 < r → r < R →
      ∀ K : Set ℂ, IsCompact K → IsConnected K → K ⊆ closedBall w R →
        CrossesAnnulus K w r R →
        (crossingComponents (K ∩ annulus w r R) w r R).Nonempty) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
      closure (cluster (μ ω) 1 0 t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 0 t))ᶜ,
        IsLocallyConnectedSet Uᶜ := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨α, _, hbound⟩ :=
    ae_centered_boundary_complement_localized_crossings_of_compact_continuum
      hI2 h6 h5 hcompactBump γ hγ hγ2
  filter_upwards [hbound α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2] with ω hcount hgeom
  intro t ht hcl U hU
  have h0 : (0 : ℂ) ∈ ball 0 1 := by simp
  have hgeo := hgeom t 1 ht zero_lt_one 0 h0 hcl U hU
  apply IsConnected.isLocallyConnectedSet_of_small_finite_crossings hgeo.2.2.1 hgeo.1.isClosed_compl
  intro x hx δ hδ
  have hxfront : x ∈ frontier U := by simpa only [frontier_compl] using hx.2
  have hevent := hcount t ht hcl U hU x hxfront
  have hevent' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∃ ρ ∈ Icc ε (Real.sqrt ε),
        (crossingComponents (Uᶜ ∩ ball x (2 * ρ)) x (ρ / 3) (2 * ρ)).encard ≤ ⌈1 / α⌉₊) ∧
      ε < (δ / 2) ^ 2 ∧ 0 < ε := by
    filter_upwards [hevent,
      (eventually_lt_nhds (sq_pos_of_pos (half_pos hδ))).filter_mono nhdsWithin_le_nhds,
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hε hsmall hpos
    exact ⟨hε, hsmall, hpos⟩
  obtain ⟨ε, ⟨ρ, hρ, hρcount⟩, hεsmall, hεpos⟩ := hevent'.exists
  have hρpos : 0 < ρ := hεpos.trans_le hρ.1
  have hsqrt : Real.sqrt ε < δ / 2 := by
    have hs := Real.sqrt_lt_sqrt hεpos.le hεsmall
    simpa [Real.sqrt_sq_eq_abs, abs_of_pos (half_pos hδ)] using hs
  refine ⟨ρ / 3, 2 * ρ, by linarith, by linarith, by linarith [hρ.2], ?_⟩
  apply Set.encard_lt_top_iff.mp
  exact hρcount.trans_lt (by simp)

end HarmonicBalls
