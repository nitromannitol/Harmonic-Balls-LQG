import HarmonicBalls.Proofs.Sec11.CorrectedPinchOpenThirdShift
import HarmonicBalls.Steps.Sec11.PinchMetricMeasureObservable

/-! # Transfer of the open-certificate pinch construction -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- The shifted metric-measure observable law transfers the positive
strengthened pinch event back to the original whole-plane observables.
The joint law comparison remains an explicit hypothesis. -/
theorem IsCorrectedPinchConfiguration.positive_internal_pinch_of_open_shiftLaw
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (γ M : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (X : Ω → Measure ℂ × {d : ℂ → ℂ → ℝ // IsEuclideanLengthMetric d})
    (hX : AEMeasurable X P)
    (hdecode : ∀ᵐ ω ∂P, (X ω).1 = μ ω ∧ (X ω).2.1 = 𝔇 (hC ω))
    (hshiftLaw : ∀ f : ℂ → ℝ, IsTestFunction univ f → (∀ x, f x ≤ 0) →
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) →
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) →
      ∃ Y : Ω → Measure ℂ × {d : ℂ → ℂ → ℝ // IsEuclideanLengthMetric d},
        AEMeasurable Y P ∧ P.map Y ≪ P.map X ∧
        (∀ᵐ ω ∂P, (Y ω).1 =
          (μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))) ∧
          (Y ω).2.1 = 𝔇 (addFunPairing (hC ω) f)))
    (hA : 0 < P {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M}) :
    0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (𝔇 (hC ω)) U T Q' Q M 1 0} := by
  obtain ⟨f, hf, hfneg, hfsupport, hfzero, hp⟩ :=
    h.exists_positive_open_first_internal_pinch_shift hξ P γ M hC hcirc 𝔇 μ h𝔇 hgff hA
  obtain ⟨Y, hY, hac, hYdecode⟩ := hshiftLaw f hf hfneg hfsupport hfzero
  let E := {p : Measure ℂ × {d : ℂ → ℂ → ℝ // IsEuclideanLengthMetric d} |
    pinchPointEventWithInternalBounds p.1 p.2.1 U T Q' Q M 1 0}
  have hE : MeasurableSet E :=
    measurableSet_pinchPointEventWithInternalBounds_on_lengthMetrics
      h.toIsPinchPointProofConfiguration.toIsPinchPointConfiguration M 0 (by norm_num)
  have hXeq : X ⁻¹' E =ᵐ[P] {ω | pinchPointEventWithInternalBounds (μ ω) (𝔇 (hC ω)) U T Q' Q M 1 0} := by
    filter_upwards [hdecode] with ω hω
    simp only [mem_preimage, mem_ofPred_eq, E, hω.1, hω.2]
  have hYeq : Y ⁻¹' E =ᵐ[P] {ω | pinchPointEventWithInternalBounds
      ((μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))))
      (𝔇 (addFunPairing (hC ω) f)) U T Q' Q M 1 0} := by
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

#print axioms IsCorrectedPinchConfiguration.positive_internal_pinch_of_open_shiftLaw
end HarmonicBalls
