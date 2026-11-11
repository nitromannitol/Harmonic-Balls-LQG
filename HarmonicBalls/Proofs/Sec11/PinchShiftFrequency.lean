import HarmonicBalls.Proofs.Sec11.PinchInitialScale
import HarmonicBalls.Proofs.Sec11.PinchShiftLaw

/-! # Fixed-point pinch frequency after a singular-field Weyl shift

The pointwise ergodic theorem used through the fixed-point bridge is due to
Leonardo Bonanno, `LatticeProb.Prob.Birkhoff`. The LQG metric, measure Weyl
scaling, and locality inputs are staged and await source check.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

open Classical in
/-- The conditional singular-field shift construction and full dyadic
stationarity imply positive fixed-point pinch frequency. The constrained
event positivity, shift realization, stationarity, and germ triviality are
explicit hypotheses. -/
theorem IsPinchPointProofConfiguration.ae_positive_pinchBlockDensity_of_shiftMap
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ α₀ M : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hweyl : LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hmloc : LQGMeasureLocality P γ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hshift : ∀ f : ℂ → ℝ, IsTestFunction univ f → (∀ x, f x ≤ 0) →
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) →
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) →
      ∃ τ : Ω → Ω, Measure.QuasiMeasurePreserving τ P P ∧
        (∀ᵐ ω ∂P, fieldCircleAverage α₀ (hcirc (τ ω)) =
          addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) f) ∧
        (∀ᵐ ω ∂P, D (τ ω) = fun x y => (weylScaling (D ω) ξ f x y).toReal))
    (hA : 0 < P {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (D ω) U V δ M ∧
      (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric (D ω) ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 x) <
        ENNReal.ofReal (setDist (D ω) Q' (frontier Q))})
    (htrivial : ∀ A : Set Ω,
      (∀ ε, 0 < ε → MeasurableSet[fieldSigmaAlgebra α₀ hC (ball 0 ε)] A) →
      P A = 0 ∨ P A = 1)
    (hstat : P.map (fun ω n => if HarmonicBalls.pinchPointEventWithInternalBounds
        (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ (n + 1)) 0 then (1 : ℝ) else 0) =
      P.map (fun ω n => if HarmonicBalls.pinchPointEventWithInternalBounds
        (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) 0 then (1 : ℝ) else 0)) :
    ∃ q ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, q * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) 0}.ncard : ℝ) := by
  have hp := h.positive_singularField_internal_pinch_of_shiftMap hξ P γ α₀ M hC hcirc D μ
    haxioms hweyl hgff hγ hγ₂ hα hD hμ hshift hA
  exact ae_positive_pinchBlockDensity_of_unitScale_stationary_lqg_event
    h.toIsPinchPointConfiguration M 0 hγ hγ₂ hα hgff hμ hD hmloc haxioms htrivial hstat hp


end HarmonicBalls
