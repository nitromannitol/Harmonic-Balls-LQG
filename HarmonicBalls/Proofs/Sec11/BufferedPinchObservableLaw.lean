import HarmonicBalls.Proofs.Sec11.SingularBufferedPinchShift

/-! # Transfer through a metric-measure observable law

A shift of the underlying sample space is not required. The absolute
continuity and the shared metric-measure observable are explicit hypotheses;
the singular metric-field axioms are staged pending source review. -/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

open Classical in
/-- Transfer a buffered pinch event using absolute continuity of the shifted
metric-measure observable law with respect to the original observable law. -/
theorem IsPinchPointProofConfiguration.positive_singular_internal_pinch_of_observableLaw
    {U V W T Q' Q : Set ℂ} {δ ξ q b : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hξ : 0 < ξ) (hq : 0 < q) (hq1 : q ≤ 1)
    {Ω Z : Type} [MeasurableSpace Ω] [MeasurableSpace Z]
    (P : Measure Ω) (γ α M : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α hC D)
    (X : Ω → Z) (ν : Z → Measure ℂ) (d : Z → ℂ → ℂ → ℝ)
    (hX : AEMeasurable X P)
    (hdecode : ∀ᵐ ω ∂P, ν (X ω) = μ ω ∧ d (X ω) = D ω)
    (hE : MeasurableSet {z | HarmonicBalls.pinchPointEventWithInternalBounds
      (ν z) (d z) U T Q' Q M 1 0})
    (hshiftLaw : ∀ f : ℂ → ℝ, IsTestFunction univ f → (∀ x, f x ≤ 0) →
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) →
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) →
      ∃ Y : Ω → Z, AEMeasurable Y P ∧ P.map Y ≪ P.map X ∧
        (∀ᵐ ω ∂P, ν (Y ω) =
            (μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))) ∧
          d (Y ω) = fun x y => (weylScaling (D ω) ξ f x y).toReal))
    (hA : 0 < P {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (D ω) U V δ M ∧
      (∀ w ∉ ball (0 : ℂ) 6, b ≤ D ω 0 w) ∧
      (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric (D ω) (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
          ENNReal.ofReal (q * b) ∧
      ENNReal.ofReal q * internalDiam (D ω) δ (thickening (3 * δ) W \ V) <
        ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}) :
    0 < P {ω | HarmonicBalls.pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' Q M 1 0} := by
  obtain ⟨f, hf, hfneg, hfsupport, hfzero, hp⟩ :=
    h.exists_positive_measure_singular_internal_pinch_of_buffer hξ hq hq1
      P γ α M hC hcirc D μ haxioms hgff hγ hγ₂ hα hD hA
  obtain ⟨Y, hY, hac, hYdecode⟩ := hshiftLaw f hf hfneg hfsupport hfzero
  let E : Set Z := {z | HarmonicBalls.pinchPointEventWithInternalBounds (ν z) (d z)
    U T Q' Q M 1 0}
  have hXeq : (X ⁻¹' E) =ᵐ[P] {ω | HarmonicBalls.pinchPointEventWithInternalBounds
      (μ ω) (D ω) U T Q' Q M 1 0} := by
    filter_upwards [hdecode] with ω hω
    simp only [mem_preimage, mem_ofPred_eq, E, hω.1, hω.2]
  have hYeq : (Y ⁻¹' E) =ᵐ[P] {ω | HarmonicBalls.pinchPointEventWithInternalBounds
      ((μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))))
      (fun x y => (weylScaling (D ω) ξ f x y).toReal) U T Q' Q M 1 0} := by
    filter_upwards [hYdecode] with ω hω
    simp only [mem_preimage, mem_ofPred_eq, E, hω.1, hω.2]
  have hYpos : 0 < P.map Y E := by
    rw [Measure.map_apply_of_aemeasurable hY hE, measure_congr hYeq]
    exact hp
  have hXpos : 0 < P.map X E := by
    by_contra hn
    have hz : P.map X E = 0 := le_antisymm (le_of_not_gt hn) (zero_le)
    exact (ne_of_gt hYpos) (hac hz)
  rwa [Measure.map_apply_of_aemeasurable hX hE, measure_congr hXeq] at hXpos


end HarmonicBalls
