import HarmonicBalls.Draft.Section11Corrected
import HarmonicBalls.Proofs.Sec11.NotMetricBall

/-! # Corrected pinch frequency and the metric-ball obstruction

The probabilistic frequency remains an explicit hypothesis. The reductions
below use the same fixed geometry supplied by that hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Corrected Lemma 11.14 follows from the staged metric-field proposition
at the physical exponent for each parameter tuple. -/
theorem corrected_pinchMetricBallConsequence_of_metricFieldAxioms
    (dγ : ℝ → ℝ)
    (haxioms : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMetricFieldAxioms P γ (γ / dγ γ) α₀ hC hcirc) :
    CorrectedPinchMetricBallConsequenceStmt.{u} dγ := by
  intro U V W T Q' Q ε hc γ α₀ hγ hγ₂ hα _ Ω _ P hC hcirc μ D hgff _ hmetric
  exact pinchEventMetricBallConsequence_of_metricFieldAxioms U T Q' Q
    hc.toIsPinchPointProofConfiguration.toIsPinchPointConfiguration
    γ α₀ (γ / dγ γ) hγ hγ₂ hα Ω P hC hcirc μ D
    (haxioms γ α₀ Ω P hC hcirc) hgff hmetric

/-- At fixed parameters, corrected pinch-scale frequency implies the
typical-boundary obstruction, conditional on the annulus comparison and the
staged metric and measure properties. -/
theorem corrected_typical_boundary_ne_metricBall
    (dγ : ℝ → ℝ) (hbound : AnnulusMassBoundByHarmonicChainStmt.{u})
    (hmany : CorrectedManyPinchScalesStmt.{u} dγ)
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ) (hdim : 0 < dγ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (Λ : Ω → ℝ → Set ℂ)
    (hmetricAxioms : LQGMetricFieldAxioms P γ (γ / dγ γ) α₀ hC hcirc)
    (hnonatomic : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hmetric : IsLQGMetricOfField P γ (γ / dγ γ) α₀ hC D)
    (hfamily : ∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) 0) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ t : ℝ, 0 < t → ∀ w : ℂ, ∀ v : ℝ, 0 < v →
      z ∈ frontier (lqgMetricBall (D ω) w v) → Λ ω t ≠ lqgMetricBall (D ω) w v := by
  obtain ⟨C, hCpos, hcomparison⟩ := hbound
  obtain ⟨U, V, W, T, Q', Q, ε, hconfig, hscales⟩ := hmany
  obtain ⟨δ, hδ, hdensity⟩ := hscales γ α₀ hγ hγ₂ hα hdim C hCpos
  filter_upwards [hcomparison γ α₀ hγ hγ₂ hα Ω P hC hcirc μ hgff hμ Λ hfamily,
    hdensity Ω P hC hcirc μ D hgff hμ hmetric,
    ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ (γ / dγ γ) α₀ hC hcirc D
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
    C v w z hconfig.toIsPinchPointProofConfiguration.toIsPinchPointConfiguration hD hnonneg hz0 hw hz
    (frequently_of_positive_dyadic_block_density _ hδ.1 hdensity)
    (fun r hr h0 => hcomparison t ht r hr z h0)

/-- Corrected Proposition 11.11 follows from the corrected pinch-frequency
statement and the displayed conditional inputs. -/
theorem corrected_harmonicBallNotMetricBall_of_comparison_and_pinch
    (dγ : ℝ → ℝ) (hbound : AnnulusMassBoundByHarmonicChainStmt.{u})
    (hmany : CorrectedManyPinchScalesStmt.{u} dγ)
    (hmetric : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMetricFieldAxioms P γ (γ / dγ γ) α₀ hC hcirc)
    (hnonatomic : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ α₀ hC hcirc) :
    CorrectedHarmonicBallNotMetricBallStmt.{u} dγ := by
  intro γ α₀ hγ hγ₂ hα hdim Ω _ P hC hcirc μ D hgff hμ hD Λ hfamily
  filter_upwards [corrected_typical_boundary_ne_metricBall dγ hbound hmany γ α₀ hγ hγ₂ hα hdim
      Ω P hC hcirc μ D Λ (hmetric γ α₀ Ω P hC hcirc) (hnonatomic γ α₀ Ω P hC hcirc)
      hgff hμ hD hfamily,
    ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ (γ / dγ γ) α₀ hC hcirc D
      (hmetric γ α₀ Ω P hC hcirc) hgff hγ hγ₂ hα hD,
    hμ, hfamily] with ω hpoint hDω hμω hfamilyω
  let : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
  have hnonneg : ∀ x y, 0 ≤ D ω x y := by
    intro x y
    have ht := hDω.triangle x y x
    rw [hDω.self_eq_zero, hDω.symm y x] at ht
    linarith
  exact ae_time_ne_metricBall_of_ae_boundary_exclusion (μ ω) (Λ ω) (D ω) 0
    hfamilyω.2 hpoint hnonneg

#print axioms corrected_typical_boundary_ne_metricBall
#print axioms corrected_harmonicBallNotMetricBall_of_comparison_and_pinch
#print axioms corrected_pinchMetricBallConsequence_of_metricFieldAxioms

end HarmonicBalls
