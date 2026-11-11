import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import HarmonicBalls.Proofs.Sec11.SingularFieldPinchWeylIdentities

/-! # Shifts of the singular-field measure and event laws

The measure Weyl-scaling input is staged and awaits source check. The shift
map and its quasi-measure-preservation are explicit assumptions.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- If a quasi-measure-preserving map implements a continuous shift of the
circle averages, uniqueness of the LQG limit identifies the shifted measure
with the Weyl-weighted measure. -/
theorem ae_lqgMeasure_comp_eq_withDensity_of_circleAverage_shift
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (f : ℂ → ℝ) (τ : Ω → Ω)
    (hweyl : LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hf : Continuous f) (hτ : Measure.QuasiMeasurePreserving τ P P)
    (hc : ∀ᵐ ω ∂P, fieldCircleAverage α₀ (hcirc (τ ω)) =
      addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) f) :
    ∀ᵐ ω ∂P, μ (τ ω) =
      (μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))) := by
  have hw := hweyl hgff hγ hγ₂ hα μ hμ
  have hm : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
  filter_upwards [hτ.ae hm, hw, hc] with ω hm hw hc
  rw [hc] at hm
  exact hm.unique (hw f hf)

/-- A positive-probability event remains positive after removing a
quasi-measure-preserving change of variables, even when the event is not
assumed measurable. -/
theorem measure_pos_of_preimage_pos_of_quasiMeasurePreserving
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (τ : Ω → Ω)
    (hτ : Measure.QuasiMeasurePreserving τ P P) (A : Set Ω)
    (hpos : 0 < P (τ ⁻¹' A)) : 0 < P A := by
  by_contra hn
  have hz : P A = 0 := le_antisymm (le_of_not_gt hn) (zero_le)
  exact (ne_of_gt hpos) (hτ.preimage_null hz)

/-- Conditional transfer of the strengthened pinch event back to the original
singular field. The explicit shift realization must supply absolute continuity,
the circle-average shift, and the metric shift for the supported smooth test functions used here.
The initial constrained event is still a separate positivity hypothesis. -/
theorem IsPinchPointProofConfiguration.positive_singularField_internal_pinch_of_shiftMap
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
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
      (∀ x ∈ Metric.closedBall 0 (3 * δ), f x = 0) →
      ∃ τ : Ω → Ω, Measure.QuasiMeasurePreserving τ P P ∧
        (∀ᵐ ω ∂P, fieldCircleAverage α₀ (hcirc (τ ω)) =
          addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) f) ∧
        (∀ᵐ ω ∂P, D (τ ω) = fun x y => (weylScaling (D ω) ξ f x y).toReal))
    (hA : 0 < P {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (D ω) U V δ M ∧
      (⨆ x ∈ Metric.sphere (0 : ℂ) 5,
        internalMetric (D ω) ((Metric.thickening (2 * δ) (Q ∪ W))ᶜ ∩ Metric.ball 0 6) 0 x) <
        ENNReal.ofReal (setDist (D ω) Q' (frontier Q))}) :
    0 < P {ω | HarmonicBalls.pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M 1 0} := by
  obtain ⟨f, htest, hfneg, hfsupport, hfzero, hp⟩ :=
    h.exists_positive_measure_singularField_internal_pinch_shift_of_metricFieldAxioms
      hξ P γ α₀ M hC hcirc D μ haxioms hgff hγ hγ₂ hα hD hA
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
