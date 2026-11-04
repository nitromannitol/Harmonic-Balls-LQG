import HarmonicBalls.Proofs.Sec11.PinchNormalizedFrequency
import HarmonicBalls.Proofs.Sec11.PinchStationarityLQG

/-! # Pinch block frequency from normalized LQG dilation

The Section 8 ergodic theorem uses Leonardo Bonanno's LatticeProb
formalization. The affine, coordinate-change and mixture metric inputs are
staged; normalized metric locality is explicit.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal

open Classical in
/-- Normalized LQG dilation yields the pinch block-frequency estimate at the
origin, conditional on metric locality. -/
theorem IsWholePlaneGFF.ae_internal_pinch_frequency_of_normalizedLQG
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → C(ℂ × ℂ, ℝ)}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α hC hcirc)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω (u, v) ∧
      ENNReal.ofReal (D ω (u, v)) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (haxioms : LQGMetricFieldAxioms (mixMeasure.prod (P.prod P)) γ ξ α
      (fun x => if x.1 = 0 then hC x.2.1 else
        affinePairing hC hcirc (((2 : ℝ)⁻¹ : ℝ) : ℂ) 0 x.2.2)
      (fun x => if x.1 = 0 then hcirc x.2.1 else
        affineCircle hcirc (((2 : ℝ)⁻¹ : ℝ) : ℂ) 0 x.2.2))
    {U T Q V : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q V) (M : ℝ)
    (hmetric : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
        (∀ᵐ ω ∂P, 0 < c ω) ∧
        (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)]
          (fun ω => G ω x y)) ∧
        (∀ᵐ ω ∂P, ∀ x ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          ∀ y ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          internalMetric (fun x y => c ω * D ω (x, y))
            (ball 0 (6 * ((2 : ℝ)⁻¹ ^ n))) x y = G ω x y))
    (δ : ℝ) (hδ : δ < (P {ω | pinchPointEventWithInternalBounds (μ ω) (fun x y => D ω (x, y))
      U T Q V M ((2 : ℝ)⁻¹ ^ 1) 0}).toReal) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (fun x y => D ω (x, y)) U T Q V M ((2 : ℝ)⁻¹ ^ n) 0}.ncard : ℝ) := by
  have hm := h.ae_lengthMetric_of_affine_mixture hAff hγ hγ₂ hα
    (k := (2 : ℝ)⁻¹) (by norm_num) 𝔇 h𝔇 hD haxioms
  have hs := h.identDistrib_pinchIndicators_of_normalizedLQG hAff hCC hγ hγ₂ hα hμ
    𝔇 h𝔇 hD haxioms hconfig M
  exact h.ae_internal_pinch_frequency_of_normalized_metric P hμ hfull hm hconfig M
    hmetric hs δ hδ

#print axioms IsWholePlaneGFF.ae_internal_pinch_frequency_of_normalizedLQG

end HarmonicBalls
