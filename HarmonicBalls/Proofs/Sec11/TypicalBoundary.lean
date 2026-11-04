import HarmonicBalls.Proofs.Sec11.PinchScales

/-! # Pinch scales at a typical boundary point -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Assuming the annulus comparison and the abundance of pinch scales,
for almost every realization and almost every LQG point, no positive-radius
metric ball having that point on its boundary equals a harmonic ball.
The metric-field and non-atomicity inputs are explicitly staged propositions. -/
theorem typical_boundary_ne_metricBall
    (hbound : AnnulusMassBoundByHarmonicChainStmt.{u})
    (hmany : ManyPinchScalesStmt.{u})
    (γ α₀ ξ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (Λ : Ω → ℝ → Set ℂ)
    (hmetricAxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hnonatomic : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hmetric : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hfamily : ∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) 0) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ t : ℝ, 0 < t → ∀ w : ℂ, ∀ v : ℝ, 0 < v →
      z ∈ frontier (lqgMetricBall (D ω) w v) → Λ ω t ≠ lqgMetricBall (D ω) w v := by
  obtain ⟨C, hCpos, hcomparison⟩ := hbound
  obtain ⟨U, T, Q', Q, hconfig, hscales⟩ := hmany
  obtain ⟨δ, hδ, hdensity⟩ := hscales γ α₀ ξ hγ hγ₂ hα C hCpos
  filter_upwards [hcomparison γ α₀ hγ hγ₂ hα Ω P hC hcirc μ hgff hμ Λ hfamily,
    hdensity Ω P hC hcirc μ D hgff hμ hmetric,
    ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      hmetricAxioms hgff hγ hγ₂ hα hmetric,
    hnonatomic hgff hγ hγ₂ hα μ hμ] with ω hcomparison hdensity hD hnonatomic
  have hz0 : ∀ᵐ z ∂(μ ω), z ≠ 0 := by
    simpa only [Set.mem_singleton_iff] using (measure_eq_zero_iff_ae_notMem.1 (hnonatomic 0))
  filter_upwards [hdensity, hz0] with z hdensity hz0
  have hnonneg : ∀ x y, 0 ≤ D ω x y := by
    intro x y
    have ht := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at ht
    linarith
  intro t ht w v hv hz
  have hw : w ≠ z := by
    intro heq
    subst w
    have hd := hD.distance_eq_of_mem_frontier_ball z z v hz
    rw [hD.self_eq_zero] at hd
    linarith
  exact ne_metricBall_of_frequently_pinch_and_annulusMassBound (μ ω) (D ω) U T Q' Q (Λ ω t)
    C v w z hconfig hD hnonneg hz0 hw hz
    (frequently_of_positive_dyadic_block_density _ hδ.1 hdensity)
    (fun r hr h0 => hcomparison t ht r hr z h0)

end HarmonicBalls
