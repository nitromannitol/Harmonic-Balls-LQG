import HarmonicBalls.Proofs.Sec11.WholePlaneMetricLocality
import HarmonicBalls.Proofs.Sec11.PinchFrequencyLQG

/-! # Whole-plane pinch frequency

The normalized metric-locality hypothesis in the frequency argument follows
for zero logarithmic charge. The Section 8 ergodic theorem uses Leonardo
Bonanno's LatticeProb code; the affine, measure-coordinate and mixture metric
inputs remain staged and pending source checking.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal

open Classical in
/-- At zero logarithmic charge, normalized LQG dilation gives pinch-block
frequency without a separate metric-locality hypothesis. -/
theorem IsWholePlaneGFF.ae_internal_pinch_frequency_zeroCharge
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → C(ℂ × ℂ, ℝ)}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω (u, v) ∧
      ENNReal.ofReal (D ω (u, v)) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -(0 : ℝ) * Real.log ‖x‖) u v)
    (haxioms : LQGMetricFieldAxioms (mixMeasure.prod (P.prod P)) γ ξ 0
      (fun x => if x.1 = 0 then hC x.2.1 else
        affinePairing hC hcirc (((2 : ℝ)⁻¹ : ℝ) : ℂ) 0 x.2.2)
      (fun x => if x.1 = 0 then hcirc x.2.1 else
        affineCircle hcirc (((2 : ℝ)⁻¹ : ℝ) : ℂ) 0 x.2.2))
    {U T Q V : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q V) (M : ℝ)
    (δ : ℝ) (hδ : δ < (P {ω | pinchPointEventWithInternalBounds (μ ω) (fun x y => D ω (x, y))
      U T Q V M ((2 : ℝ)⁻¹ ^ 1) 0}).toReal) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (fun x y => D ω (x, y)) U T Q V M
          ((2 : ℝ)⁻¹ ^ n) 0}.ncard : ℝ) := by
  have hα : (0 : ℝ) < lqgQ γ := by
    unfold lqgQ
    positivity
  have hd : IsLQGMetricOfField P γ ξ 0 hC (fun ω x y => D ω (x, y)) :=
    ⟨𝔇, h𝔇, hD⟩
  have hmetric := h.exists_modConst_dyadic_internalMetrics_zeroCharge hd
  exact h.ae_internal_pinch_frequency_of_normalizedLQG hAff hCC hγ hγ₂ hα hμ hfull
    𝔇 h𝔇 hD haxioms hconfig M hmetric δ hδ


end HarmonicBalls
