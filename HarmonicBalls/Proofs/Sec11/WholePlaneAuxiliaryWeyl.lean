import HarmonicBalls.Steps.Sec11.PinchMeasureWeylShift
import HarmonicBalls.Proofs.Sec11.WholePlanePinchThirdEvent

/-! # Simultaneous whole-plane auxiliary events after a Weyl shift

The initial intersection of the first two auxiliary events is an explicit
positive-measure hypothesis. The result concerns the weighted measure and the
metric of the shifted whole-plane field; change of law remains separate.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- If the first two auxiliary events occur on a positive-measure set, one
smooth deterministic Weyl shift makes all three occur on a positive-measure
set for the shifted whole-plane metric and the weighted measure. -/
theorem IsPinchPointProofConfiguration.exists_positive_measure_wholePlane_auxiliary_shift
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (γ M : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (hA : 0 < P {ω | pinchFirstEvent (𝔇 (hC ω)) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M}) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧ (∀ x, f x ≤ 0) ∧
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) ∧
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) ∧
      0 < P {ω | pinchFirstEvent (𝔇 (addFunPairing (hC ω) f)) W T Q' Q δ ∧
        pinchSecondEvent ((μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))))
          (𝔇 (addFunPairing (hC ω) f)) U V δ M ∧
        pinchThirdEvent (𝔇 (addFunPairing (hC ω) f)) V W δ} := by
  let A : Set Ω := {ω | pinchFirstEvent (𝔇 (hC ω)) W T Q' Q δ ∧
    pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M}
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
  exact ⟨h.pinchFirstEvent_of_weylScaling hd he hξ.le hfneg hfinner hfouter hz
      hforward hzeroE hreverse hω.1.1.1,
    h.pinchSecondEvent_of_weighted_weylScaling hd he hξ.le hfneg hfzero hz
      hforward hzeroE hreverse hω.1.1.2, hω.1.2⟩

end HarmonicBalls
