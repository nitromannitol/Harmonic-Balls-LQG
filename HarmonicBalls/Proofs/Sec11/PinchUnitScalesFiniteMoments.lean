import HarmonicBalls.Proofs.Sec11.PinchUnitFrequencyLQG
import HarmonicBalls.Proofs.Sec11.DyadicLocalityFiniteMoments
import HarmonicBalls.Steps.Sec11.PositiveBlockDensity
import HarmonicBalls.Steps.Sec11.ScalePowerBounds

/-! # Pinch scales from unit-scale probability and finite moments

The Section 8 ergodic theorem and Section 6 assembly used here include
Leonardo Bonanno's LatticeProb formalization. The whole-plane mass bound,
measure existence and coordinate-change inputs, and the mixture metric-field
axioms are staged and remain subject to source review. -/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal

open Classical in
/-- At Liouville charge, finitely many base-metric diameter moments and
positive unit-scale internal-pinch probability imply arbitrarily small
internal and original pinch scales. -/
theorem IsWholePlaneGFF.exists_small_pinch_scales_of_unit_probability_and_finite_moments
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → C(ℂ × ℂ, ℝ)}
    (h : IsWholePlaneGFF P hC hcirc)
    (hDG : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (γ' : ℝ)
      (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P' γ' hC' hcirc')
    (hCC0 : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (γ' : ℝ)
      (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P' γ' 0 hC' hcirc')
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc)
    (hCC : LQGMeasureCoordChange P γ γ hC hcirc)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hξ : 0 < ξ)
    (hμ : IsLQGMeasureOfField P γ γ hcirc μ)
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
    (hpos : 0 < P {ω | pinchPointEventWithInternalBounds (μ ω)
      (fun x y => D ω (x, y)) U T Q V M 1 0}) :
    ∃ (ε : ℝ) (N : ℕ) (z : ℕ → ℂ), 0 < ε ∧
      ((∀ i, i ≤ N → (∫⁻ ω, ⨆ x ∈ closedBall (z i) ε,
        ⨆ y ∈ closedBall (z i) ε,
          internalMetric (𝔇 (hC ω)) (ball (z i) (2 * ε)) x y ∂P) ≠ ∞) →
        ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∃ n : ℕ, ((2 : ℝ)⁻¹) ^ n < r ∧
          pinchPointEventWithInternalBounds (μ ω) (fun x y => D ω (x, y))
            U T Q V M ((2 : ℝ)⁻¹ ^ n) 0 ∧
          pinchPointEvent (μ ω) (fun x y => D ω (x, y))
            U T Q V M ((2 : ℝ)⁻¹ ^ n) 0) := by
  have hα := gamma_lt_lqgQ hγ hγ₂
  have hAff := wholePlaneGFFAffineInvariance_proved P hC hcirc
  have hm := h.ae_lengthMetric_of_affine_mixture hAff hγ hγ₂ hα
    (k := (2 : ℝ)⁻¹) (by norm_num) 𝔇 h𝔇 hD haxioms
  obtain ⟨ε, N, z, hε, hlocal⟩ :=
    h.exists_dyadic_locality_criterion_of_finite_diameter_moments hAff 𝔇 h𝔇 hD hm hξ hγ.le hα
  refine ⟨ε, N, z, hε, ?_⟩
  intro hmom
  obtain ⟨δ, hδ, hfreq⟩ := h.ae_positive_internal_pinch_frequency_of_lqg_inputs
    hDG hCC0 hE0 hCC hγ hγ₂ hα hμ 𝔇 h𝔇 hD haxioms hconfig M (hlocal hmom) hpos
  filter_upwards [hfreq, hm] with ω hω hmetric r hr
  obtain ⟨n, hn, hevent⟩ := exists_small_dyadic_scale_of_positive_block_density hδ.1 hω r hr
  exact ⟨n, hn, hevent, pinchPointEvent_of_internalBounds hmetric hevent⟩


end HarmonicBalls
