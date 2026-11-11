import HarmonicBalls.Steps.Sec11.InternalPinchFixedPoint
import HarmonicBalls.Proofs.Sec8.BirkhoffPort

/-! # Fixed-point pinch-scale density via Birkhoff's theorem

The pointwise ergodic theorem used here is from Leonardo Bonanno's
LatticeProb formalization, `LatticeProb.Prob.Birkhoff`.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter

open Classical in
/-- The fixed-point pinch density with internal bounds follows from one-scale positivity,
stationarity, field-germ triviality, and the staged metric and measure
locality inputs. The pointwise Birkhoff premise is supplied by LatticeProb. -/
theorem ae_positive_internal_pinchBlockDensity_of_stationary_lqg_event_birkhoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ ξ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hmloc : LQGMeasureLocality P γ α₀ hC hcirc)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (htrivial : ∀ A : Set Ω,
      (∀ ε, 0 < ε → MeasurableSet[fieldSigmaAlgebra α₀ hC (ball z ε)] A) →
      P A = 0 ∨ P A = 1)
    (hstat : P.map (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
        ((2 : ℝ)⁻¹ ^ (n + 2)) z then (1 : ℝ) else 0) =
      P.map (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
        ((2 : ℝ)⁻¹ ^ (n + 1)) z then (1 : ℝ) else 0))
    (hpos : 0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' Q M ((2 : ℝ)⁻¹ ^ 1) z}) :
    ∃ δ ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ) := by
  let F : Ω → ℕ → ℝ := fun ω n =>
    if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
      ((2 : ℝ)⁻¹ ^ (n + 1)) z then 1 else 0
  let : IsFiniteMeasure (P.map F) := P.isFiniteMeasure_map F
  apply ae_positive_internal_pinchBlockDensity_of_stationary_lqg_event hconfig M z hγ hγ₂ hα
    hgff hμ hD hmloc haxioms htrivial
  · exact pointwiseBirkhoff_of_latticeProb _ _ _
  · exact hstat
  · exact hpos


end HarmonicBalls
