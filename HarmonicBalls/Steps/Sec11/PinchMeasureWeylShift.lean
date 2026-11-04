import HarmonicBalls.Steps.Sec11.PinchFirstWeylPreservation
import HarmonicBalls.Steps.Sec11.PinchLocalData

/-! # Weyl shifts of the measure in the second auxiliary event

A perturbation supported in the inner annulus and vanishing on `U` does not
change either the mass of `U` or the annular Green-potential supremum.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter
open scoped ENNReal

/-- A Weyl-weighted measure agrees with the original measure on any
measurable set where the perturbation vanishes. -/
theorem restrict_withDensity_exp_eq_of_eq_zero (μ : Measure ℂ) (γ : ℝ)
    (f : ℂ → ℝ) {S : Set ℂ} (hS : MeasurableSet S)
    (hf : ∀ x ∈ S, f x = 0) :
    (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x)))).restrict S =
      μ.restrict S := by
  rw [restrict_withDensity hS]
  have heq : (fun x => ENNReal.ofReal (Real.exp (γ * f x))) =ᵐ[μ.restrict S] 1 := by
    filter_upwards [ae_restrict_mem hS] with x hx
    simp only [hf x hx, mul_zero, Real.exp_zero, ENNReal.ofReal_one, Pi.one_apply]
  rw [withDensity_congr_ae heq, withDensity_one]

/-- The supported shift leaves the two measure terms in the second auxiliary
event unchanged. -/
theorem IsPinchPointProofConfiguration.weylShift_measure_terms_eq
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (μ : Measure ℂ) (γ : ℝ) (f : ℂ → ℝ)
    (hf : ∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) :
    (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x)))) U = μ U ∧
    annulusGreenPotentialSup
      (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x)))) 0 3 6 =
      annulusGreenPotentialSup μ 0 3 6 := by
  have hU := restrict_withDensity_exp_eq_of_eq_zero μ γ f h.isOpen_U.measurableSet
    (fun x hx => hf x (Or.inl (subset_closure hx)))
  have hmass := congrArg (fun ν : Measure ℂ => ν U) hU
  have hAnn : ∀ x ∈ annulus (0 : ℂ) 3 6, f x = 0 := by
    intro x hx
    apply hf x (Or.inr ?_)
    intro hy
    have hxlarge : (3 : ℝ) < dist x 0 := lt_of_not_ge hx.2
    have hysmall : dist x (0 : ℂ) < 2 := hy.1
    linarith
  refine ⟨?_, annulusGreenPotentialSup_eq_of_restrict_eq 0 3 6
    (restrict_withDensity_exp_eq_of_eq_zero μ γ f (measurableSet_ball.diff measurableSet_closedBall) hAnn)⟩
  simpa only [Measure.restrict_apply h.isOpen_U.measurableSet, inter_self] using hmass

/-- Under the metric identities, a supported nonpositive Weyl perturbation
preserves the entire second auxiliary event for the weighted measure. -/
theorem IsPinchPointProofConfiguration.pinchSecondEvent_of_weighted_weylScaling
    {U V W T Q' Q : Set ℂ} {δ ξ γ M : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hξ : 0 ≤ ξ) {f : ℂ → ℝ}
    (hfneg : ∀ x, f x ≤ 0)
    (hf : ∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0)
    (hzeroD : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hforward : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hzeroE : ∀ x y, weylScaling E ξ 0 x y = ENNReal.ofReal (E x y))
    (hreverse : ∀ x y, ENNReal.ofReal (D x y) =
      weylScaling E ξ (fun z => -f z) x y)
    {μ : Measure ℂ} (hevent : pinchSecondEvent μ D U V δ M) :
    pinchSecondEvent (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x)))) E U V δ M := by
  have hfinner : ∀ x ∈ ball (0 : ℂ) 1, f x = 0 := by
    intro x hx
    apply hf x (Or.inr ?_)
    intro hxann
    have hxsmall : dist x (0 : ℂ) < 1 := hx
    have hxlarge : 1 < dist x (0 : ℂ) := lt_of_not_ge hxann.2
    linarith
  obtain ⟨hmass, hpotential⟩ := h.weylShift_measure_terms_eq μ γ f hf
  exact h.pinchSecondEvent_of_weylScaling hD hE hξ hfneg hfinner hzeroD hforward
    hzeroE hreverse hmass hpotential hevent

end HarmonicBalls
