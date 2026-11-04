import HarmonicBalls.Steps.Sec11.PinchBufferedThirdBump
import HarmonicBalls.Steps.Sec11.WholePlaneWeylShift

/-! # A whole-plane Weyl shift with a buffered pinch barrier

The joint positive-measure assumption includes both quantitative margins.
This result does not establish that assumption or transfer the shifted law.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- A common positive-measure event with both strict margins yields a
positive-measure strengthened pinch event after one deterministic shift. -/
theorem IsPinchPointProofConfiguration.exists_positive_measure_wholePlane_internal_pinch_of_buffer
    {U V W T Q' Q : Set ℂ} {δ ξ q b : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hξ : 0 < ξ) (hq : 0 < q) (hq1 : q ≤ 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (γ M : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (hA : 0 < P {ω | pinchFirstEvent (𝔇 (hC ω)) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M ∧
      (∀ w ∉ ball (0 : ℂ) 6, b ≤ 𝔇 (hC ω) 0 w) ∧
      (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric (𝔇 (hC ω)) (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
          ENNReal.ofReal (q * b) ∧
      ENNReal.ofReal q * internalDiam (𝔇 (hC ω)) δ (thickening (3 * δ) W \ V) <
        ENNReal.ofReal (setDist (𝔇 (hC ω)) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧ (∀ x, f x ≤ 0) ∧
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) ∧
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) ∧
      0 < P {ω | HarmonicBalls.pinchPointEventWithInternalBounds
        ((μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))))
        (𝔇 (addFunPairing (hC ω) f)) U T Q' Q M 1 0} := by
  obtain ⟨f, htest, hbound, hfzero, hfdisk, hproduce⟩ :=
    h.exists_smooth_weight_for_internal_pinch hξ hq hq1
  let A : Set Ω := {ω | pinchFirstEvent (𝔇 (hC ω)) W T Q' Q δ ∧
    pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M ∧
    (∀ w ∉ ball (0 : ℂ) 6, b ≤ 𝔇 (hC ω) 0 w) ∧
    (⨆ x ∈ sphere (0 : ℂ) 5,
      internalMetric (𝔇 (hC ω)) (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
        ENNReal.ofReal (q * b) ∧
    ENNReal.ofReal q * internalDiam (𝔇 (hC ω)) δ (thickening (3 * δ) W \ V) <
      ENNReal.ofReal (setDist (𝔇 (hC ω)) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}
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
  have heq : A =ᵐ[P] A ∩ G := by
    filter_upwards [hG] with ω hω
    simp only [mem_inter_iff, hω, and_true]
  have hp : 0 < P (A ∩ G) := by rw [← measure_congr heq]; exact hA
  refine ⟨f, htest, (fun x => (hbound x).2), hfzero, hfdisk,
    hp.trans_le (measure_mono ?_)⟩
  intro ω hω
  obtain ⟨hd, he, hz, hforward, hzeroE, hreverse⟩ := hω.2
  have henonneg : ∀ x y, 0 ≤ 𝔇 (addFunPairing (hC ω) f) x y := by
    intro x y
    have ht := he.triangle x y x
    rw [he.self_eq_zero, he.symm y x] at ht
    linarith
  exact hproduce _ _ _ γ M b hd he henonneg hz hforward hzeroE hreverse
    hω.1.1 hω.1.2.1 hω.1.2.2.1 hω.1.2.2.2.1 hω.1.2.2.2.2

#print axioms IsPinchPointProofConfiguration.exists_positive_measure_wholePlane_internal_pinch_of_buffer

end HarmonicBalls
