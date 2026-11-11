import HarmonicBalls.Proofs.Sec11.PinchFrequencyLQG
import HarmonicBalls.Proofs.Sec11.PinchRecenteredRootLaw

/-! # LQG pinch frequencies at measure-typical points

The origin estimate uses Leonardo Bonanno's LatticeProb ergodic theorem.
The affine, coordinate-change and mixture metric inputs are staged. Rooted
and recentered comparisons remain explicit hypotheses.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal

open Classical in
/-- A single normalized origin estimate transfers to LQG-typical points under
rooted and recentered comparison hypotheses, with the same deterministic rate. -/
theorem IsWholePlaneGFF.ae_ae_pinch_frequency_of_normalizedLQG
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
    (P₀ : Measure Ω) [SFinite P₀]
    (hμ₀ : AEMeasurable μ P₀) (hloc₀ : ∀ᵐ ω ∂(P₀), IsLocallyFiniteMeasure (μ ω))
    (hDmeas : ∀ x y, Measurable fun ω => D ω (x, y))
    (hmetric₀ : ∀ᵐ ω ∂(P₀), IsEuclideanLengthMetric (fun x y => D ω (x, y)))
    (ν : ℕ → Measure Ω) (hμν : ∀ n, AEMeasurable μ (ν n))
    (hlocν : ∀ n, ∀ᵐ ω ∂(ν n), IsLocallyFiniteMeasure (μ ω))
    (hmetricν : ∀ n, ∀ᵐ ω ∂(ν n), IsEuclideanLengthMetric (fun x y => D ω (x, y)))
    (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hpos : ∀ z, w z ≠ 0) (hfin : ∀ z, w z ≠ ∞)
    (ρ : ℕ → Measure ℂ) (shift : ℕ → ℂ × Ω → Ω)
    (hshift : ∀ n, Measurable (shift n)) (R : ℕ → ℂ → Measure Ω)
    (hrooted : ∀ n, P₀ ⊗ₘ (unnormalizedWeightedRestrictionKernel P₀ μ hμ₀
      (weightedLocalization w n) (measurableSet_weightedLocalization hw n) w hw) ≪
        shiftedRootReferenceLaw (ρ n) P₀ (shift n))
    (hac : ∀ n, ∀ᵐ z ∂(ρ n), P₀.map (fun ω => shift n (z, ω)) ≪ R n z)
    (hdom : ∀ n, ∀ᵐ z ∂(ρ n), R n z ≪ ν n)
    (recenter : ℂ → Ω → Ω) (hrec : ∀ n, ∀ᵐ z ∂(ρ n), AEMeasurable (recenter z) (R n z))
    (hcomp : ∀ n, ∀ᵐ z ∂(ρ n), (R n z).map (recenter z) ≪ P)
    (heq : ∀ n, ∀ᵐ z ∂(ρ n), ∀ᵐ ω ∂(R n z),
      μ (recenter z ω) = (μ ω).map (fun y : ℂ => y - z) ∧
        ∀ x y, D (recenter z ω) (x, y) = D ω (x + z, y + z)) :
    ∀ᵐ ω ∂(P₀), ∀ᵐ z ∂(μ ω), ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEvent (μ ω) (fun x y => D ω (x, y)) U T Q V M
          ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ) := by
  have hf := h.ae_internal_pinch_frequency_of_normalizedLQG hAff hCC hγ hγ₂ hα hμ
    hfull 𝔇 h𝔇 hD haxioms hconfig M hmetric δ hδ
  exact ae_ae_pinch_block_density_of_recentered_rooted_law P₀ hμ₀ hloc₀ hDmeas hmetric₀
    ν hμν hlocν hmetricν hconfig M δ w hw hpos hfin ρ shift hshift R hrooted
    hac hdom recenter hrec P hcomp heq hf


end HarmonicBalls
