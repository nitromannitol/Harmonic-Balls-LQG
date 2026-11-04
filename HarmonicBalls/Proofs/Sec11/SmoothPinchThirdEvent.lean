import HarmonicBalls.Steps.Sec11.PinchSmoothWeylBump
import HarmonicBalls.Steps.Sec11.PinchThirdThresholds
import HarmonicBalls.Steps.Sec11.WeylFieldZero

/-! # Positive-measure third event after a smooth Weyl shift

A deterministic strict contraction is chosen on a positive-measure subevent.
The transformed metric, its Weyl identity, and the sphere-gap comparison are
explicit hypotheses. No change-of-law or positivity of the initial event is
assumed as a literature input here. -/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- A single smooth compactly supported weight produces the third auxiliary
pinch event on a positive-measure subevent, assuming the stated properties of
the shifted metric and the sphere-gap comparison. -/
theorem IsPinchPointProofConfiguration.exists_positive_measure_smooth_shift_thirdEvent
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (D : Ω → ℂ → ℂ → ℝ) (E : (ℂ → ℝ) → Ω → ℂ → ℂ → ℝ)
    (hA : 0 < P A)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hzero : ∀ᵐ ω ∂P, ∀ x y, weylScaling (D ω) ξ 0 x y = ENNReal.ofReal (D ω x y))
    (hshift : ∀ f : ℂ → ℝ, IsTestFunction univ f →
      (∀ x, f x ≤ 0) → (∀ x ∈ closedBall 0 (3 * δ), f x = 0) →
      ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E f ω) ∧
        (∀ x y, 0 ≤ E f ω x y) ∧
        (∀ x y, ENNReal.ofReal (E f ω x y) = weylScaling (D ω) ξ f x y) ∧
        ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) ≤
          ENNReal.ofReal (setDist (E f ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧ (∀ x, f x ≤ 0) ∧
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) ∧
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) ∧
      0 < P {ω | ω ∈ A ∧ pinchThirdEvent (E f ω) V W δ} := by
  obtain ⟨q, hq, hq1, hp⟩ := h.exists_positive_measure_third_contraction P A D hA hD
  obtain ⟨f, hfsmooth, hfcompact, hfneg, hweight, hfzero, hfdisk⟩ :=
    h.exists_smooth_third_weyl_weight hξ hq hq1
  have hftest : IsTestFunction univ f := ⟨hfsmooth, hfcompact, subset_univ _⟩
  let B : Set Ω := {ω | ω ∈ A ∧
    ENNReal.ofReal q * internalDiam (D ω) δ (thickening (3 * δ) W \ V) <
      ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}
  let G : Set Ω := {ω | IsEuclideanLengthMetric (D ω) ∧
    (∀ x y, weylScaling (D ω) ξ 0 x y = ENNReal.ofReal (D ω x y)) ∧
    IsEuclideanLengthMetric (E f ω) ∧ (∀ x y, 0 ≤ E f ω x y) ∧
    (∀ x y, ENNReal.ofReal (E f ω x y) = weylScaling (D ω) ξ f x y) ∧
    ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) ≤
      ENNReal.ofReal (setDist (E f ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}
  have hG : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [hD, hzero, hshift f hftest hfneg hfdisk] with ω hd hz hs
    exact ⟨hd, hz, hs⟩
  have heq : B =ᵐ[P] B ∩ G := by
    filter_upwards [hG] with ω hω
    simp only [mem_inter_iff, hω, and_true]
  have hp' : 0 < P (B ∩ G) := by rw [← measure_congr heq]; exact hp
  refine ⟨f, hftest, hfneg, hfzero, hfdisk, hp'.trans_le (measure_mono ?_)⟩
  intro ω hω
  obtain ⟨hd, hz, he, henonneg, hscale, hgap⟩ := hω.2
  refine ⟨hω.1.1, ?_⟩
  apply hd.pinchThirdEvent_of_weylScaling he henonneg V W hz hscale (B := Real.log q)
  · intro z hz'
    exact (hweight z hz').le
  · exact hgap
  · simpa only [Real.exp_log hq] using hω.1.2

/-- For a logarithmically singular LQG field, the staged metric-field
axioms discharge the original length-metric and zero-weight premises. The
shifted metric and sphere-gap premises remain explicit. -/
theorem IsPinchPointProofConfiguration.exists_positive_measure_smooth_lqg_shift_thirdEvent
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (E : (ℂ → ℝ) → Ω → ℂ → ℂ → ℝ)
    (hA : 0 < P A)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hshift : ∀ f : ℂ → ℝ, IsTestFunction univ f →
      (∀ x, f x ≤ 0) → (∀ x ∈ closedBall 0 (3 * δ), f x = 0) →
      ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E f ω) ∧
        (∀ x y, 0 ≤ E f ω x y) ∧
        (∀ x y, ENNReal.ofReal (E f ω x y) = weylScaling (D ω) ξ f x y) ∧
        ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) ≤
          ENNReal.ofReal (setDist (E f ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧ (∀ x, f x ≤ 0) ∧
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) ∧
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) ∧
      0 < P {ω | ω ∈ A ∧ pinchThirdEvent (E f ω) V W δ} := by
  apply h.exists_positive_measure_smooth_shift_thirdEvent hξ P A D E hA
  · exact ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      haxioms hgff hγ hγ₂ hα hD
  · exact ae_weylScaling_zero_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      haxioms hgff hγ hγ₂ hα hD
  · exact hshift

end HarmonicBalls
