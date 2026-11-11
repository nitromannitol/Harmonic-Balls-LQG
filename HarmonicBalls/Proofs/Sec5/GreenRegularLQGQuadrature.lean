import HarmonicBalls.Proofs.Sec5.GreenRegularNestedDomains
import HarmonicBalls.Proofs.Sec5.GeneralDomainGreenQuadrature
import HarmonicBalls.Proofs.Sec9.DyadicGlobalUniqueness

/-!
# LQG quadrature in Green-regular domains

Compact containment transfers disc frontier nullity to general domains. The
Green-function and obstacle arguments use work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open Filter MeasureTheory Metric Set
open scoped Topology

universe u

/-- On one field event, every compactly contained cluster in a bounded
Green-regular domain has null frontier, full mass, and quadrature. -/
theorem ae_greenRegular_clusterOn_quadrature
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (U : Set ℂ), IsOpen U → Bornology.IsBounded U →
      ∀ (z : ℂ), z ∈ U → ∀ (t : ℝ), 0 < t →
      (∀ y ∈ closure U, y ∉ U → Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0)) →
      closure (clusterOn (μ ω) U z t) ⊆ U →
      μ ω (frontier (clusterOn (μ ω) U z t)) = 0 ∧
      μ ω (clusterOn (μ ω) U z t) = ENNReal.ofReal t ∧
      IsHarmonicBallGen (μ ω) (clusterOn (μ ω) U z t) z ∧
      ∀ (O : Set ℂ) (q : ℂ → ℝ), IsOpen O →
        closure (clusterOn (μ ω) U z t) ⊆ O → ContinuousOn q O → IsSubharmonicOn O q →
        Integrable q ((μ ω).restrict (clusterOn (μ ω) U z t)) ∧
        t * q z ≤ ∫ x, q x ∂(μ ω).restrict (clusterOn (μ ω) U z t) := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, clusterBoundaryNullAllRadii_of_dyadic_typical_scales hI2 h611 h82 hAff
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hvol hnull
  intro U hU hbounded z hz t ht hreg hcl
  obtain ⟨R, hsub⟩ := hbounded.subset_ball (0 : ℂ)
  have hR : 0 < R := (norm_nonneg z).trans_lt (mem_ball_zero_iff.mp (hsub hz))
  have hv := leastSupersolutionOn_mem_of_greenRegular hvol.1 hR (hvol.2 R hR)
    hU hsub hz ht hreg
  have heq := clusterOn_eq_cluster_of_compact_containment hU hsub hz ht hv hcl
  have hfront : μ ω (frontier (clusterOn (μ ω) U z t)) = 0 := by
    rw [heq]
    apply hnull R t hR ht z (hsub hz)
    rw [← heq]
    exact hcl.trans hsub
  refine ⟨hfront, (general_clusterOn_harmonic_quadrature_of_frontier_null hvol.1 hR
    (hvol.2 R hR) hU hsub hz ht hcl hfront).1,
    general_clusterOn_isHarmonicBallGen_of_frontier_null hvol.1 hR (hvol.2 R hR)
      hU hsub hz ht hcl hfront, ?_⟩
  intro O q hO hΛO hq hqsub
  exact general_clusterOn_subharmonic_quadrature_of_frontier_null hvol.1 hR (hvol.2 R hR)
    hU hsub hz ht hcl hfront hO hΛO hq hqsub

end HarmonicBalls
