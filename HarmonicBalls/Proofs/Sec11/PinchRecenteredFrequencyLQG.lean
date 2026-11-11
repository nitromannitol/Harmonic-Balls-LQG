import HarmonicBalls.Proofs.Sec11.PinchFrequencyLQG
import HarmonicBalls.Proofs.Sec11.PinchRecenteredRootLaw

/-! # Pinch frequencies under recentered comparison laws

The origin estimate uses Leonardo Bonanno's LatticeProb ergodic theorem. The
LQG affine, coordinate-change and mixture metric inputs are staged. The
recentered absolute-continuity comparison is an explicit hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal

open Classical in
/-- The origin block-frequency estimate transfers to a fixed root under a
recentered comparison law, with no assumed stationarity at that root. -/
theorem IsWholePlaneGFF.ae_internal_pinch_frequency_of_recentered_normalizedLQG
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
      U T Q V M ((2 : ℝ)⁻¹ ^ 1) 0}).toReal)
    (R : Measure Ω) (z : ℂ) (recenter : Ω → Ω)
    (hrec : AEMeasurable recenter R) (hac : R.map recenter ≪ P)
    (heq : ∀ᵐ ω ∂(R), μ (recenter ω) = (μ ω).map (fun y : ℂ => y - z) ∧
      ∀ x y, D (recenter ω) (x, y) = D ω (x + z, y + z)) :
    ∀ᵐ ω ∂(R), ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (fun x y => D ω (x, y)) U T Q V M
          ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ) := by
  have hf := h.ae_internal_pinch_frequency_of_normalizedLQG hAff hCC hγ hγ₂ hα hμ
    hfull 𝔇 h𝔇 hD haxioms hconfig M hmetric δ hδ
  exact ae_internal_pinch_block_density_of_recentered_comparison R P U T Q V M δ
    (fun k => (2 : ℝ)⁻¹ ^ k) z recenter hrec hac heq hf


end HarmonicBalls
