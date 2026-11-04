import HarmonicBalls.Steps.Sec11.WeylBoundaryGap
import HarmonicBalls.Steps.Sec11.PinchWeylMonotonicity
import HarmonicBalls.Steps.Sec11.PinchDistancePositivity

/-! # Preservation of the first auxiliary pinch event

A nonpositive Weyl perturbation decreases internal distances. If it vanishes
on neighborhoods of the two boundaries, the corresponding lower bounds for
set distances are preserved by the inverse Weyl identity.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory
open scoped ENNReal

/-- A nonpositive Weyl shift preserving neighborhoods of `Q` and the origin
preserves the first auxiliary pinch event. -/
theorem IsPinchPointProofConfiguration.pinchFirstEvent_of_weylScaling
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hξ : 0 ≤ ξ) {f : ℂ → ℝ}
    (hfneg : ∀ x, f x ≤ 0) (hfinner : ∀ x ∈ ball 0 1, f x = 0)
    (hfouter : ∀ x ∈ (closedBall 0 3)ᶜ, f x = 0)
    (hzeroD : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hforward : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hzeroE : ∀ x y, weylScaling E ξ 0 x y = ENNReal.ofReal (E x y))
    (hreverse : ∀ x y, ENNReal.ofReal (D x y) =
      weylScaling E ξ (fun z => -f z) x y)
    (hevent : pinchFirstEvent D W T Q' Q δ) : pinchFirstEvent E W T Q' Q δ := by
  have horder : ∀ x y, ENNReal.ofReal (E x y) ≤ ENNReal.ofReal (D x y) := by
    intro x y
    rw [hforward x y, ← hzeroD x y]
    apply weylScaling_mono_exponent
    intro z
    simpa only [Pi.zero_apply, mul_zero] using mul_nonpos_of_nonneg_of_nonpos hξ (hfneg z)
  have hδ : 0 < δ := h.δ₀_mem.1
  have hQcl : closure Q ⊆ (closedBall (0 : ℂ) 3)ᶜ := by
    have hsub := (closure_subset_thickening (by positivity : 0 < 10 * δ) Q).trans
      (subset_closure.trans h.thickening_Q)
    intro x hx hxball
    have hxann := (hsub hx).1
    have hxlarge : (4 : ℝ) < dist x 0 := lt_of_not_ge hxann.2
    have hxsmall : dist x (0 : ℂ) ≤ 3 := hxball
    linarith
  have hQne : Q ≠ univ := by
    intro heq
    have hz : (0 : ℂ) ∈ Q := by rw [heq]; exact mem_univ _
    exact (h.Q_subset hz).1.2 (by simp)
  have hfrontQ : (frontier Q).Nonempty :=
    nonempty_frontier_iff.mpr ⟨h.isConnected_Q.nonempty, hQne⟩
  have hgapQ := ofReal_setDist_boundary_le_of_inverse_weylScaling hD hE h.isOpen_Q
    isClosed_closedBall.isOpen_compl (subset_closure.trans h.closure_Q'_subset) hQcl
    h.isConnected_Q'.nonempty hfrontQ hfouter hzeroE hreverse
  have hδ1 : δ < 1 := by linarith [h.δ₀_mem.2]
  have hballcl : closure (ball (0 : ℂ) δ) ⊆ ball 0 1 := by
    rw [closure_ball 0 hδ.ne']
    intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball]
    linarith
  have hfrontδ : (frontier (ball (0 : ℂ) δ)).Nonempty := by
    rw [frontier_ball 0 hδ.ne']
    exact NormedSpace.sphere_nonempty.mpr hδ.le
  have hgap0 := ofReal_setDist_boundary_le_of_inverse_weylScaling hD hE isOpen_ball
    isOpen_ball (singleton_subset_iff.mpr (mem_ball_self hδ)) hballcl
    (singleton_nonempty 0) hfrontδ hfinner hzeroE hreverse
  rw [frontier_ball 0 hδ.ne'] at hgap0
  constructor
  · apply lt_of_le_of_lt ?_ (hevent.1.trans_le hgapQ)
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    exact le_iSup_of_le x (le_iSup_of_le hx (internalMetric_le_of_ofReal_le horder _ _ _))
  · exact (internalDiam_le_of_ofReal_le horder _ _).trans_lt (hevent.2.trans_le hgap0)

/-- The second auxiliary event is preserved if the mass of `U` and the
annular Green-potential supremum are preserved as well. -/
theorem IsPinchPointProofConfiguration.pinchSecondEvent_of_weylScaling
    {U V W T Q' Q : Set ℂ} {δ ξ M : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hξ : 0 ≤ ξ) {f : ℂ → ℝ}
    (hfneg : ∀ x, f x ≤ 0) (hfinner : ∀ x ∈ ball 0 1, f x = 0)
    (hzeroD : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hforward : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hzeroE : ∀ x y, weylScaling E ξ 0 x y = ENNReal.ofReal (E x y))
    (hreverse : ∀ x y, ENNReal.ofReal (D x y) =
      weylScaling E ξ (fun z => -f z) x y)
    {μ ν : Measure ℂ} (hmass : ν U = μ U)
    (hpotential : annulusGreenPotentialSup ν 0 3 6 = annulusGreenPotentialSup μ 0 3 6)
    (hevent : pinchSecondEvent μ D U V δ M) : pinchSecondEvent ν E U V δ M := by
  have horder : ∀ x y, ENNReal.ofReal (E x y) ≤ ENNReal.ofReal (D x y) := by
    intro x y
    rw [hforward x y, ← hzeroD x y]
    apply weylScaling_mono_exponent
    intro z
    simpa only [Pi.zero_apply, mul_zero] using mul_nonpos_of_nonneg_of_nonpos hξ (hfneg z)
  have hδ : 0 < δ := h.δ₀_mem.1
  have hδ2 : 0 < 2 * δ := by positivity
  have hballcl : closure (ball (0 : ℂ) (2 * δ)) ⊆ ball 0 1 := by
    rw [closure_ball 0 hδ2.ne']
    intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball]
    linarith [h.δ₀_mem.2]
  have hsphere : sphere (0 : ℂ) δ ⊆ ball 0 (2 * δ) := by
    intro x hx
    rw [mem_sphere] at hx
    rw [mem_ball]
    linarith
  have hfront : (frontier (ball (0 : ℂ) (2 * δ))).Nonempty := by
    rw [frontier_ball 0 hδ2.ne']
    exact NormedSpace.sphere_nonempty.mpr hδ2.le
  have hgap := ofReal_setDist_boundary_le_of_inverse_weylScaling hD hE isOpen_ball
    isOpen_ball hsphere hballcl (NormedSpace.sphere_nonempty.mpr hδ.le)
    hfront hfinner hzeroE hreverse
  rw [frontier_ball 0 hδ2.ne'] at hgap
  refine ⟨(internalDiam_le_of_ofReal_le horder _ _).trans_lt (hevent.1.trans_le hgap), ?_⟩
  simpa only [hmass, hpotential] using hevent.2

end HarmonicBalls
