import HarmonicBalls.Steps.Sec11.PinchGermIndicator
import HarmonicBalls.Steps.Sec11.InternalPinchPositiveDensityAE

/-! # Fixed-point pinch-scale density -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter

open Classical in
/-- The local LQG pinch event with internal bounds has positive scale density at a fixed point
provided its dyadic indicator law is stationary, the field germ is trivial,
and Birkhoff's theorem and one-scale positivity hold. -/
theorem ae_positive_internal_pinchBlockDensity_of_stationary_lqg_event
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
    (hBirkhoff : PointwiseBirkhoff (P.map (fun ω n =>
      if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
        ((2 : ℝ)⁻¹ ^ (n + 1)) z then (1 : ℝ) else 0))
      (fun x n => x (n + 1)) (fun x => x 0))
    (hstat : P.map (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
        ((2 : ℝ)⁻¹ ^ (n + 2)) z then (1 : ℝ) else 0) =
      P.map (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
        ((2 : ℝ)⁻¹ ^ (n + 1)) z then (1 : ℝ) else 0))
    (hpos : 0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' Q M ((2 : ℝ)⁻¹ ^ 1) z}) :
    ∃ δ ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ) := by
  obtain ⟨X, hXm, hbound, hX, hXgerm⟩ :=
    exists_germ_measurable_pinchIndicators hconfig M z hγ hγ₂ hα hgff hμ hD hmloc haxioms
  have heq1 : P.map (fun ω n => X (n + 1) ω) =
      P.map (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
        ((2 : ℝ)⁻¹ ^ (n + 1)) z then (1 : ℝ) else 0) := by
    apply Measure.map_congr
    filter_upwards [hX] with ω hω
    funext n
    exact hω (n + 1)
  have heq2 : P.map (fun ω n => X (n + 2) ω) =
      P.map (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
        ((2 : ℝ)⁻¹ ^ (n + 2)) z then (1 : ℝ) else 0) := by
    apply Measure.map_congr
    filter_upwards [hX] with ω hω
    funext n
    exact hω (n + 2)
  have hb : PointwiseBirkhoff (P.map (fun ω n => X (n + 1) ω))
      (fun x n => x (n + 1)) (fun x => x 0) := by
    unfold PointwiseBirkhoff at hBirkhoff ⊢
    rw [heq1]
    exact hBirkhoff
  have hs : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω) := by
    rw [heq2, heq1]
    exact hstat
  exact ae_eventually_internal_pinch_positive_block_density_of_ae_rep P μ D U T Q' Q M z X
    (fun ε => fieldSigmaAlgebra α₀ hC (ball z ε))
    (fun ε _ => hgff.fieldSigmaAlgebra_le α₀ (ball z ε)) hXgerm htrivial hXm hbound hX hb hs hpos

#print axioms ae_positive_internal_pinchBlockDensity_of_stationary_lqg_event

end HarmonicBalls
