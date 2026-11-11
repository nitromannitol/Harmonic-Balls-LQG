import HarmonicBalls.Proofs.Sec11.SingularBufferedPinchShift
import HarmonicBalls.Proofs.Sec11.PinchShiftLaw

/-! # Transfer of a buffered pinch event through a field shift

The simultaneous strict margins and the shift realization are explicit
hypotheses. The metric and measure Weyl-scaling inputs are staged and await
source checking.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- A positive-measure buffered auxiliary event gives the strengthened pinch
 event under the original singular-field law when a compatible quasi-measure-
 preserving shift is available. -/
theorem IsPinchPointProofConfiguration.positive_singular_internal_pinch_of_buffer_shiftMap
    {U V W T Q' Q : Set ℂ} {δ ξ q b : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hξ : 0 < ξ) (hq : 0 < q) (hq1 : q ≤ 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ M : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hweyl : LQGMeasureWeylScaling P γ α₀ hC hcirc)
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
      (∀ w ∉ ball (0 : ℂ) 6, b ≤ D ω 0 w) ∧
      (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric (D ω) (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
          ENNReal.ofReal (q * b) ∧
      ENNReal.ofReal q * internalDiam (D ω) δ (thickening (3 * δ) W \ V) <
        ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}) :
    0 < P {ω | HarmonicBalls.pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M 1 0} := by
  obtain ⟨f, htest, hfneg, hfsupport, hfzero, hp⟩ :=
    h.exists_positive_measure_singular_internal_pinch_of_buffer hξ hq hq1
      P γ α₀ M hC hcirc D μ haxioms hgff hγ hγ₂ hα hD hA
  obtain ⟨τ, hτ, hc, hd⟩ := hshift f htest hfneg hfsupport hfzero
  have hm := ae_lqgMeasure_comp_eq_withDensity_of_circleAverage_shift
    P γ α₀ hC hcirc μ f τ hweyl hgff hγ hγ₂ hα hμ htest.1.continuous hτ hc
  let A : Set Ω := {ω | HarmonicBalls.pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M 1 0}
  have heq : (τ ⁻¹' A) =ᵐ[P] {ω | HarmonicBalls.pinchPointEventWithInternalBounds
      ((μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))))
      (fun x y => (weylScaling (D ω) ξ f x y).toReal) U T Q' Q M 1 0} := by
    filter_upwards [hm, hd] with ω hm hd
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, A]
    rw [hm, hd]
  have hp' : 0 < P (τ ⁻¹' A) := by rw [measure_congr heq]; exact hp
  exact measure_pos_of_preimage_pos_of_quasiMeasurePreserving P τ hτ A hp'


end HarmonicBalls
