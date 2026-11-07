import HarmonicBalls.Proofs.Sec11.CorrectedPinchFrequency
import HarmonicBalls.Proofs.Sec11.DyadicLocalityPositiveMoments

/-! # Local pinch witnesses from positive diameter moments

The Section 8 inputs use Leonardo Bonanno's LatticeProb formalization.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- A positive moment, rather than a first moment, suffices for the local
Liouville-charge pinch witness. The metric-field axiom remains staged, while
the moment bound and positive internal-pinch probability remain obligations. -/
theorem exists_local_internal_pinch_liouvilleCharge_of_positive_moments
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {γ ξ : ℝ}
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q) (M p : ℝ)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ γ hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (haxioms : LQGMetricFieldAxioms P γ ξ γ hC hcirc)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hξ : 0 < ξ) (hp : 0 < p)
    (hD : IsLQGMetricOfField P γ ξ γ hC D)
    (hpos : 0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M 1 0}) :
    ∃ (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), IsLQGMetric γ ξ 𝔇 ∧
      ∃ (ε : ℝ) (N : ℕ) (z : ℕ → ℂ), 0 < ε ∧
        ((∀ i, i ≤ N → (∫⁻ ω, (⨆ x ∈ closedBall (z i) ε,
          ⨆ y ∈ closedBall (z i) ε,
            internalMetric (𝔇 (hC ω)) (ball (z i) (2 * ε)) x y) ^ p ∂P) ≠ ∞) →
          (∃ E : Set Ω, MeasurableSet[Section6.fieldSigmaAlgebraModConst γ hC (ball 0 7)] E ∧
            0 < P E ∧ ∀ᵐ ω ∂P, ω ∈ E → pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0) ∧
          (∃ E ⊆ {ω | pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0}, MeasurableSet E ∧ 0 < P E)) := by
  have hAff := wholePlaneGFFAffineInvariance_proved P hC hcirc
  have hγQ := gamma_lt_lqgQ hγ hγ₂
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ γ hC hcirc D
    haxioms hgff hγ hγ₂ hγQ hD
  obtain ⟨𝔇, h𝔇, hrepr⟩ := hD
  have hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (D ω x y) =
      weylScaling (𝔇 (hC ω)) ξ (fun z => -γ * Real.log ‖z‖) x y := by
    filter_upwards [hrepr] with ω hω
    exact fun x y => (hω x y).2
  have hball : ball (0 : ℂ) (Real.exp (1 - (1 : ℝ))) ⊆ ball 0 6 := by
    simp only [sub_self, Real.exp_zero]
    exact ball_subset_ball (by norm_num)
  obtain ⟨ε, N, z, hε, hremove⟩ :=
    hgff.exists_puncture_criterion_of_lqgMetric_positive_moments hAff 𝔇 h𝔇 D 1 γ p
      (by norm_num) hξ hγ.le hγQ hp (ball 0 6) hball hmetric hscale
  refine ⟨𝔇, h𝔇, ε, N, z, hε, ?_⟩
  intro hmom
  obtain ⟨ψ, hψ, hψint⟩ := IsTestFunction.exists_integral_eq_one
    (isOpen_ball : IsOpen (ball (0 : ℂ) 7)) ⟨0, mem_ball_self (by norm_num)⟩
  have hne : (ball (0 : ℂ) 6 \ {0}).Nonempty := by
    refine ⟨1, ?_⟩
    norm_num [Metric.mem_ball, dist_eq_norm]
  have hlocal := hgff.exists_modConst_internal_singularMetric_of_point_removal
    𝔇 h𝔇 hrepr hmetric (V := ball (0 : ℂ) 6) (U := ball 0 7)
    isOpen_ball hne (ball_subset_ball (by norm_num)) ψ hψ hψint (by
      filter_upwards [hremove hmom] with ω hω x hx y hy
      exact hω x y (by simpa using hx.2) (by simpa using hy.2))
  obtain ⟨c, G, hc, hG, hGeq⟩ := hlocal
  exact exists_local_internal_pinch_of_metric_locality P hC hcirc μ D hconfig M
    hgff hμ hfull c G hc hmetric hG hGeq hpos

#print axioms exists_local_internal_pinch_liouvilleCharge_of_positive_moments

end HarmonicBalls
