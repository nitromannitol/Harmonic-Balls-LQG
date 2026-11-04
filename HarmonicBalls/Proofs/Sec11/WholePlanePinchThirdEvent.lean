import HarmonicBalls.Steps.Sec11.WholePlaneWeylShift
import HarmonicBalls.Steps.Sec11.PinchThirdThresholds

/-! # Smooth Weyl shift for the whole-plane third event

The result applies to a whole-plane GFF. It produces the third event after a
shift on a positive-measure subevent of an arbitrary positive-measure set;
it does not transfer that set or the event under a change of law.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- A deterministic smooth shift produces the third auxiliary pinch event on
part of any positive-measure event for a whole-plane GFF metric. -/
theorem IsPinchPointProofConfiguration.exists_positive_measure_wholePlane_shift_thirdEvent
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (hA : 0 < P A) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧ (∀ x, f x ≤ 0) ∧
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) ∧
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) ∧
      0 < P {ω | ω ∈ A ∧ pinchThirdEvent (𝔇 (addFunPairing (hC ω) f)) V W δ} := by
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
    filter_upwards [ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 hgff
      (fun _ _ => 0) (by intro ω; fun_prop) (by intro x; fun_prop)] with ω hω
    exact hω.1
  obtain ⟨q, hq, hq1, hp⟩ :=
    h.exists_positive_measure_third_contraction P A (fun ω => 𝔇 (hC ω)) hA hmetric
  obtain ⟨f, hfsmooth, hfcompact, hfneg, hweight, hfzero, hfdisk⟩ :=
    h.exists_smooth_third_weyl_weight hξ hq hq1
  have hfb : ∀ x ∈ ball (0 : ℂ) 1, f x = 0 := by
    intro x hx
    apply hfzero x (Or.inr ?_)
    intro hxann
    have hxsmall : dist x (0 : ℂ) < 1 := hx
    have hxlarge : 1 < dist x (0 : ℂ) := lt_of_not_ge hxann.2
    linarith
  let B : Set Ω := {ω | ω ∈ A ∧
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
      (fun _ => f) (by intro ω; exact hfsmooth.continuous) (by intro x; fun_prop)
  have heq : B =ᵐ[P] B ∩ G := by
    filter_upwards [hG] with ω hω
    simp only [mem_inter_iff, hω, and_true]
  have hp' : 0 < P (B ∩ G) := by rw [← measure_congr heq]; exact hp
  refine ⟨f, ⟨hfsmooth, hfcompact, subset_univ _⟩, hfneg, hfzero, hfdisk,
    hp'.trans_le (measure_mono ?_)⟩
  intro ω hω
  obtain ⟨hd, he, hz, hscale, hzeroE, hinverse⟩ := hω.2
  have henonneg : ∀ x y, 0 ≤ 𝔇 (addFunPairing (hC ω) f) x y := by
    intro x y
    have ht := he.triangle x y x
    rw [he.self_eq_zero, he.symm y x] at ht
    linarith
  have hgap := ofReal_setDist_pinch_spheres_le_of_inverse_weylScaling hd he
    h.δ₀_mem.1 (show 3 * δ < 1 by linarith [h.δ₀_mem.2]) hfb hzeroE hinverse
  refine ⟨hω.1.1, ?_⟩
  apply hd.pinchThirdEvent_of_weylScaling he henonneg V W hz hscale (B := Real.log q)
  · intro z hz'
    exact (hweight z hz').le
  · exact hgap
  · simpa only [Real.exp_log hq] using hω.1.2

end HarmonicBalls
