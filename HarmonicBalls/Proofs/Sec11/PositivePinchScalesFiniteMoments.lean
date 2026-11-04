import HarmonicBalls.Proofs.Sec11.DyadicLocalityFiniteMoments
import HarmonicBalls.Steps.Sec11.PinchClearanceProbability
import HarmonicBalls.Steps.Sec11.PositiveBlockDensity

/-! # Arbitrarily small pinch scales at Liouville charge

The conclusion depends on finitely many diameter moments and an explicit
bound for global pinch events without boundary clearance. The Section 8 inputs
use Leonardo Bonanno's LatticeProb code.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal

open Classical in
/-- At `α = γ`, positive block frequency of the internal-bound event yields
arbitrarily small scales with both the internal and original pinch events. -/
theorem IsWholePlaneGFF.exists_small_pinch_scales_of_finite_moments_and_clearance_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → C(ℂ × ℂ, ℝ)}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ γ hC hcirc)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hξ : 0 < ξ)
    (hμ : IsLQGMeasureOfField P γ γ hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω (u, v) ∧
      ENNReal.ofReal (D ω (u, v)) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -γ * Real.log ‖x‖) u v)
    (haxioms : LQGMetricFieldAxioms (mixMeasure.prod (P.prod P)) γ ξ γ
      (fun x => if x.1 = 0 then hC x.2.1 else
        affinePairing hC hcirc (((2 : ℝ)⁻¹ : ℝ) : ℂ) 0 x.2.2)
      (fun x => if x.1 = 0 then hcirc x.2.1 else
        affineCircle hcirc (((2 : ℝ)⁻¹ : ℝ) : ℂ) 0 x.2.2))
    {U T Q V : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q V) (M : ℝ)
    (hbound : P ({ω | IsEuclideanLengthMetric (fun x y => D ω (x, y)) ∧
        (∀ x y, 0 ≤ D ω (x, y)) ∧
        pinchPointEvent (μ ω) (fun x y => D ω (x, y)) U T Q V M ((2 : ℝ)⁻¹ ^ 1) 0} \
      {ω | PinchBoundaryClearance (fun x y => D ω (x, y)) T ((2 : ℝ)⁻¹ ^ 1) 0}) <
      P {ω | IsEuclideanLengthMetric (fun x y => D ω (x, y)) ∧
        (∀ x y, 0 ≤ D ω (x, y)) ∧
        pinchPointEvent (μ ω) (fun x y => D ω (x, y)) U T Q V M ((2 : ℝ)⁻¹ ^ 1) 0}) :
    ∃ (ε : ℝ) (N : ℕ) (z : ℕ → ℂ), 0 < ε ∧
      ((∀ i, i ≤ N → (∫⁻ ω, ⨆ x ∈ closedBall (z i) ε,
        ⨆ y ∈ closedBall (z i) ε,
          internalMetric (𝔇 (hC ω)) (ball (z i) (2 * ε)) x y ∂P) ≠ ∞) →
        ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∃ n : ℕ, ((2 : ℝ)⁻¹) ^ n < r ∧
          pinchPointEventWithInternalBounds (μ ω) (fun x y => D ω (x, y))
            U T Q V M ((2 : ℝ)⁻¹ ^ n) 0 ∧
          pinchPointEvent (μ ω) (fun x y => D ω (x, y))
            U T Q V M ((2 : ℝ)⁻¹ ^ n) 0) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  obtain ⟨δ, hδpos, hδ⟩ := exists_positive_pinch_rate_of_clearance_failure_bound
    P μ (fun ω x y => D ω (x, y)) U T Q V M ((2 : ℝ)⁻¹ ^ 1) 0 hbound
  have hα := gamma_lt_lqgQ hγ hγ₂
  have hm := h.ae_lengthMetric_of_affine_mixture hAff hγ hγ₂ hα
    (k := (2 : ℝ)⁻¹) (by norm_num) 𝔇 h𝔇 hD haxioms
  obtain ⟨ε, N, z, hε, hfreq⟩ := h.exists_pinch_frequency_criterion_of_finite_diameter_moments
    hAff hCC hγ hγ₂ hξ hγ.le hα hμ hfull 𝔇 h𝔇 hD haxioms hconfig M δ hδ
  refine ⟨ε, N, z, hε, ?_⟩
  intro hmom
  filter_upwards [hfreq hmom, hm] with ω hf hmetric r hr
  obtain ⟨n, hn, hevent⟩ := exists_small_dyadic_scale_of_positive_block_density hδpos hf r hr
  exact ⟨n, hn, hevent, pinchPointEvent_of_internalBounds hmetric hevent⟩

#print axioms IsWholePlaneGFF.exists_small_pinch_scales_of_finite_moments_and_clearance_bound

end HarmonicBalls
