import HarmonicBalls.Steps.Sec11.PinchConstrainedBarrier
import HarmonicBalls.Steps.Sec11.PinchFirstWeylPreservation
import HarmonicBalls.Steps.Sec11.WeylBumpTopology
import HarmonicBalls.Steps.Sec11.PinchMeasureWeylShift
import HarmonicBalls.Steps.Sec11.PinchSmoothWeylBump

/-! # Boundary barriers under a Weyl shift

A bounded nonpositive Weyl perturbation preserves a boundary barrier after
accounting for its global contraction factor. The required strict margin and
the occurrence of the auxiliary events remain explicit.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal ContDiff

/-- A two-sided comparison transfers a buffered boundary barrier and a
uniform obstacle-avoiding path bound to the smaller metric. -/
theorem IsEuclideanLengthMetric.pinchConstrainedPaths_of_metric_comparison
    {D E : ℂ → ℂ → ℝ} (hE : IsEuclideanLengthMetric E)
    (hEnonneg : ∀ x y, 0 ≤ E x y) {c b : ℝ} (hc : 0 ≤ c)
    (hlower : ∀ x y, c * D x y ≤ E x y)
    (hupper : ∀ x y, E x y ≤ D x y)
    (W Q' Q : Set ℂ) (δ : ℝ)
    (hclear : ∀ w ∉ ball (0 : ℂ) 6, b ≤ D 0 w)
    (hfirst : (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric E (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
      ENNReal.ofReal (setDist E Q' (frontier Q)))
    (hmargin : (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric D (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
      ENNReal.ofReal (c * b)) :
    (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric E ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 x) <
      ENNReal.ofReal (setDist E Q' (frontier Q)) := by
  apply hE.pinchConstrainedPaths_of_barrier hEnonneg W Q' Q δ (c * b) ?_ hfirst ?_
  · intro w hw
    exact (mul_le_mul_of_nonneg_left (hclear w hw) hc).trans (hlower 0 w)
  · apply lt_of_le_of_lt ?_ hmargin
    refine iSup_le fun x => iSup_le fun hx => ?_
    apply (internalMetric_le_of_ofReal_le (fun x y => ENNReal.ofReal_le_ofReal (hupper x y))
      _ _ _).trans
    exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)

/-- A nonpositive bounded Weyl bump preserves the constrained-path estimate
when the original paths have a margin below the contracted barrier. -/
theorem IsEuclideanLengthMetric.pinchConstrainedPaths_of_weyl_barrier
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hEnonneg : ∀ x y, 0 ≤ E x y)
    {ξ a b : ℝ} (hξ : 0 ≤ ξ) (f : ℂ → ℝ)
    (hl : ∀ z, a ≤ f z) (hu : ∀ z, f z ≤ 0)
    (hzero : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (W Q' Q : Set ℂ) (δ : ℝ)
    (hclear : ∀ w ∉ ball (0 : ℂ) 6, b ≤ D 0 w)
    (hfirst : (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric E (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
      ENNReal.ofReal (setDist E Q' (frontier Q)))
    (hmargin : (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric D (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
      ENNReal.ofReal (Real.exp (ξ * a) * b)) :
    (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric E ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 x) <
      ENNReal.ofReal (setDist E Q' (frontier Q)) := by
  apply hE.pinchConstrainedPaths_of_metric_comparison hEnonneg (Real.exp_nonneg _) ?_ ?_
    W Q' Q δ hclear hfirst hmargin
  · intro x y
    have hb := (weylScaling_negative_bump_real_bounds hD hξ f hl hu hzero x y).2.1
    rw [← hscale x y, ENNReal.toReal_ofReal (hEnonneg x y)] at hb
    exact hb
  · intro x y
    have hb := (weylScaling_negative_bump_real_bounds hD hξ f hl hu hzero x y).2.2
    rw [← hscale x y, ENNReal.toReal_ofReal (hEnonneg x y)] at hb
    exact hb

/-- The first two auxiliary events, a buffered barrier, and the third event
for the shifted metric imply the strengthened pinch event after the shift. -/
theorem IsPinchPointProofConfiguration.pinchPointEventWithInternalBounds_of_weyl_barrier
    {U V W T Q' Q : Set ℂ} {δ ξ γ M a b : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hEnonneg : ∀ x y, 0 ≤ E x y)
    (hξ : 0 ≤ ξ) {f : ℂ → ℝ} (hl : ∀ z, a ≤ f z) (hu : ∀ z, f z ≤ 0)
    (hf : ∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0)
    (hzeroD : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hforward : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hzeroE : ∀ x y, weylScaling E ξ 0 x y = ENNReal.ofReal (E x y))
    (hreverse : ∀ x y, ENNReal.ofReal (D x y) =
      weylScaling E ξ (fun z => -f z) x y)
    {μ : MeasureTheory.Measure ℂ}
    (hfirst : pinchFirstEvent D W T Q' Q δ)
    (hsecond : pinchSecondEvent μ D U V δ M)
    (hthird : pinchThirdEvent E V W δ)
    (hclear : ∀ w ∉ ball (0 : ℂ) 6, b ≤ D 0 w)
    (hmargin : (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric D (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
      ENNReal.ofReal (Real.exp (ξ * a) * b)) :
    HarmonicBalls.pinchPointEventWithInternalBounds
      (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))))
      E U T Q' Q M 1 0 := by
  have hfinner : ∀ x ∈ ball (0 : ℂ) 1, f x = 0 := by
    intro x hx
    apply hf x (Or.inr ?_)
    intro hxann
    have hxsmall : dist x (0 : ℂ) < 1 := hx
    have hxlarge : 1 < dist x (0 : ℂ) := lt_of_not_ge hxann.2
    linarith
  have hfouter : ∀ x ∈ (closedBall (0 : ℂ) 3)ᶜ, f x = 0 := by
    intro x hx
    apply hf x (Or.inr ?_)
    intro hxann
    have hxlarge : (3 : ℝ) < dist x 0 := lt_of_not_ge hx
    have hxsmall : dist x (0 : ℂ) < 2 := hxann.1
    linarith
  have hfirstE := h.pinchFirstEvent_of_weylScaling hD hE hξ hu hfinner hfouter
    hzeroD hforward hzeroE hreverse hfirst
  have hsecondE := h.pinchSecondEvent_of_weighted_weylScaling hD hE hξ hu hf
    hzeroD hforward hzeroE hreverse hsecond (γ := γ)
  apply h.pinchPointEventWithInternalBounds hE hEnonneg _ M hfirstE hsecondE hthird
  exact hD.pinchConstrainedPaths_of_weyl_barrier hE hEnonneg hξ f hl hu
    hzeroD hforward W Q' Q δ hclear hfirstE.1 hmargin

/-- The smooth third-event weight can be chosen with an explicit global
lower bound corresponding to its prescribed contraction factor. -/
theorem IsPinchPointProofConfiguration.exists_smooth_third_weyl_weight_with_lower_bound
    {U V W T Q' Q : Set ℂ} {δ ξ q : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hξ : 0 < ξ) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ x, Real.log q / ξ ≤ f x ∧ f x ≤ 0) ∧
      (∀ x ∈ thickening δ (thickening (3 * δ) W \ V), ξ * f x = Real.log q) ∧
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) ∧
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) := by
  obtain ⟨φ, hφsmooth, hφcompact, hφone, hφzero, hφrange⟩ :=
    h.exists_smooth_third_weyl_bump
  let a : ℝ := Real.log q / ξ
  let f : ℂ → ℝ := fun x => a * φ x
  have ha : a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hq.le hq1) hξ.le
  have hfzero : ∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0 := by
    intro x hx
    simp [f, hφzero x hx]
  refine ⟨f, contDiff_const.mul hφsmooth, hφcompact.mul_left, ?_, ?_, hfzero, ?_⟩
  · intro x
    constructor
    · change a ≤ a * φ x
      nlinarith [(hφrange x).2]
    · exact mul_nonpos_of_nonpos_of_nonneg ha (hφrange x).1
  · intro x hx
    simp only [f, hφone x hx, mul_one, a]
    field_simp
  · intro x hx
    apply hfzero x (Or.inr ?_)
    intro hxann
    have hxlarge : 1 < dist x (0 : ℂ) := lt_of_not_ge hxann.2
    have hxsmall : dist x (0 : ℂ) ≤ 3 * δ := hx
    linarith [h.δ₀_mem.2]


end HarmonicBalls
