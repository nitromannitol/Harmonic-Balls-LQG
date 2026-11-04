import HarmonicBalls.Steps.Sec11.PinchMeasureWeylShift
import HarmonicBalls.Steps.Sec11.PinchConstrainedWeylShift
import HarmonicBalls.Steps.Sec11.PinchProofAssembly
import HarmonicBalls.Proofs.Sec11.WholePlanePinchThirdEvent

/-! # Whole-plane strengthened pinch event after a Weyl shift

The initial first and second auxiliary events and constrained-path inequality
are an explicit positive-measure hypothesis. The result concerns the weighted measure and the
metric of the shifted whole-plane field; change of law remains separate.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- If the first two auxiliary events and the constrained-path inequality
occur on a positive-measure set, a smooth deterministic Weyl shift produces
the strengthened pinch event on a positive-measure set. -/
theorem IsPinchPointProofConfiguration.exists_positive_measure_wholePlane_internal_pinch_shift
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (γ M : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (hA : 0 < P {ω | pinchFirstEvent (𝔇 (hC ω)) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M ∧
      (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric (𝔇 (hC ω)) ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 x) <
        ENNReal.ofReal (setDist (𝔇 (hC ω)) Q' (frontier Q))}) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧ (∀ x, f x ≤ 0) ∧
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) ∧
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) ∧
      0 < P {ω | HarmonicBalls.pinchPointEventWithInternalBounds
        ((μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))))
        (𝔇 (addFunPairing (hC ω) f)) U T Q' Q M 1 0} := by
  let A : Set Ω := {ω | pinchFirstEvent (𝔇 (hC ω)) W T Q' Q δ ∧
    pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M ∧
      (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric (𝔇 (hC ω)) ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 x) <
        ENNReal.ofReal (setDist (𝔇 (hC ω)) Q' (frontier Q))}
  obtain ⟨f, htest, hfneg, hfzero, hfdisk, hp⟩ :=
    h.exists_positive_measure_wholePlane_shift_thirdEvent hξ P A γ hC hcirc 𝔇 h𝔇 hgff hA
  have hfinner : ∀ x ∈ ball (0 : ℂ) 1, f x = 0 := by
    intro x hx
    apply hfzero x (Or.inr ?_)
    intro hxann
    have hxsmall : dist x (0 : ℂ) < 1 := hx
    have hxlarge : 1 < dist x (0 : ℂ) := lt_of_not_ge hxann.2
    linarith
  have hfouter : ∀ x ∈ (closedBall (0 : ℂ) 3)ᶜ, f x = 0 := by
    intro x hx
    apply hfzero x (Or.inr ?_)
    intro hxann
    have hxlarge : (3 : ℝ) < dist x 0 := lt_of_not_ge hx
    have hxsmall : dist x (0 : ℂ) < 2 := hxann.1
    linarith
  let B : Set Ω := {ω | ω ∈ A ∧ pinchThirdEvent (𝔇 (addFunPairing (hC ω) f)) V W δ}
  let G : Set Ω := {ω | IsEuclideanLengthMetric (𝔇 (hC ω)) ∧
    IsEuclideanLengthMetric (𝔇 (addFunPairing (hC ω) f)) ∧
    (∀ x y, weylScaling (𝔇 (hC ω)) ξ 0 x y = ENNReal.ofReal (𝔇 (hC ω) x y)) ∧
    (∀ x y, ENNReal.ofReal (𝔇 (addFunPairing (hC ω) f) x y) =
      weylScaling (𝔇 (hC ω)) ξ f x y) ∧
    (∀ x y, weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ 0 x y =
      ENNReal.ofReal (𝔇 (addFunPairing (hC ω) f) x y)) ∧
    (∀ x y, ENNReal.ofReal (𝔇 (hC ω) x y) =
      weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -f z) x y)}
  have hG : ∀ᵐ ω ∂P, ω ∈ G := by
    exact ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 hgff
      (fun _ => f) (by intro ω; exact htest.1.continuous) (by intro x; fun_prop)
  have heq : B =ᵐ[P] B ∩ G := by
    filter_upwards [hG] with ω hω
    simp only [mem_inter_iff, hω, and_true]
  have hp' : 0 < P (B ∩ G) := by rw [← measure_congr heq]; exact hp
  refine ⟨f, htest, hfneg, hfzero, hfdisk, hp'.trans_le (measure_mono ?_)⟩
  intro ω hω
  obtain ⟨hd, he, hz, hforward, hzeroE, hreverse⟩ := hω.2
  have hnonneg : ∀ x y, 0 ≤ 𝔇 (addFunPairing (hC ω) f) x y := by
    intro x y
    have ht := he.triangle x y x
    rw [he.self_eq_zero, he.symm y x] at ht
    linarith
  apply h.pinchPointEventWithInternalBounds he hnonneg _ M
  · exact h.pinchFirstEvent_of_weylScaling hd he hξ.le hfneg hfinner hfouter hz
      hforward hzeroE hreverse hω.1.1.1
  · exact h.pinchSecondEvent_of_weighted_weylScaling hd he hξ.le hfneg hfzero hz
      hforward hzeroE hreverse hω.1.1.2.1
  · exact hω.1.2
  · exact h.pinchConstrainedPaths_of_weylScaling hd he hξ.le hfneg hfouter hz
      hforward hzeroE hreverse hω.1.1.2.2

end HarmonicBalls
