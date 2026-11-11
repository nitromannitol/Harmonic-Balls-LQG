import HarmonicBalls.Steps.Sec11.PinchBarrierWeylShift

/-! # A single smooth bump for both pinch margins

The contraction factor used for the third auxiliary event also fixes the
amount by which a boundary barrier may shrink. Both strict margins are
assumed; their simultaneous positive probability is not asserted.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal ContDiff

/-- A single deterministic smooth Weyl weight produces the strengthened
pinch event for every metric and measure satisfying the two displayed margins
and the Weyl identities. -/
theorem IsPinchPointProofConfiguration.exists_smooth_weight_for_internal_pinch
    {U V W T Q' Q : Set ℂ} {δ ξ q : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hξ : 0 < ξ) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧
      (∀ x, Real.log q / ξ ≤ f x ∧ f x ≤ 0) ∧
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) ∧
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) ∧
      ∀ (D E : ℂ → ℂ → ℝ) (μ : MeasureTheory.Measure ℂ) (γ M b : ℝ),
        IsEuclideanLengthMetric D → IsEuclideanLengthMetric E →
        (∀ x y, 0 ≤ E x y) →
        (∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y)) →
        (∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y) →
        (∀ x y, weylScaling E ξ 0 x y = ENNReal.ofReal (E x y)) →
        (∀ x y, ENNReal.ofReal (D x y) = weylScaling E ξ (fun z => -f z) x y) →
        pinchFirstEvent D W T Q' Q δ → pinchSecondEvent μ D U V δ M →
        (∀ w ∉ ball (0 : ℂ) 6, b ≤ D 0 w) →
        (⨆ x ∈ sphere (0 : ℂ) 5,
          internalMetric D (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) < ENNReal.ofReal (q * b) →
        ENNReal.ofReal q * internalDiam D δ (thickening (3 * δ) W \ V) <
          ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) →
        HarmonicBalls.pinchPointEventWithInternalBounds
          (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x)))) E U T Q' Q M 1 0 := by
  obtain ⟨f, hfsmooth, hfsupp, hfbound, hweight, hfzero, hfdisk⟩ :=
    h.exists_smooth_third_weyl_weight_with_lower_bound hξ hq hq1
  refine ⟨f, ⟨hfsmooth, hfsupp, subset_univ _⟩, hfbound, hfzero, hfdisk, ?_⟩
  intro D E μ γ M b hD hE hEnonneg hzeroD hforward hzeroE hreverse
    hfirst hsecond hclear hmargin hstrict
  have hfinner : ∀ x ∈ ball (0 : ℂ) 1, f x = 0 := by
    intro x hx
    apply hfzero x (Or.inr ?_)
    intro hxann
    have hxsmall : dist x (0 : ℂ) < 1 := hx
    have hxlarge : 1 < dist x (0 : ℂ) := lt_of_not_ge hxann.2
    linarith
  have hgap := ofReal_setDist_pinch_spheres_le_of_inverse_weylScaling hD hE
    h.δ₀_mem.1 (show 3 * δ < 1 by linarith [h.δ₀_mem.2]) hfinner hzeroE hreverse
  have hthird : pinchThirdEvent E V W δ := by
    apply hD.pinchThirdEvent_of_weylScaling hE hEnonneg V W hzeroD hforward
      (B := Real.log q)
    · intro z hz
      exact (hweight z hz).le
    · exact hgap
    · simpa only [Real.exp_log hq] using hstrict
  have hfactor : Real.exp (ξ * (Real.log q / ξ)) = q := by
    rw [mul_div_cancel₀ _ (ne_of_gt hξ), Real.exp_log hq]
  apply h.pinchPointEventWithInternalBounds_of_weyl_barrier hD hE hEnonneg hξ.le
    (fun z => (hfbound z).1) (fun z => (hfbound z).2) hfzero hzeroD hforward
    hzeroE hreverse hfirst hsecond hthird hclear
  simpa only [hfactor] using hmargin


end HarmonicBalls
