import HarmonicBalls.Steps.Sec11.PinchFirstWeylPreservation

/-! # Weyl preservation of the constrained-path inequality

The inequality remains strict when internal distances decrease and the
`Q'`-to-boundary distance is preserved by inverse Weyl scaling.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- The radius-six constrained-path inequality is preserved by a nonpositive
Weyl shift which vanishes outside the closed radius-three ball. -/
theorem IsPinchPointProofConfiguration.pinchConstrainedPaths_of_weylScaling
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hξ : 0 ≤ ξ) {f : ℂ → ℝ}
    (hfneg : ∀ x, f x ≤ 0)
    (hfouter : ∀ x ∈ (closedBall 0 3)ᶜ, f x = 0)
    (hzeroD : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hforward : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hzeroE : ∀ x y, weylScaling E ξ 0 x y = ENNReal.ofReal (E x y))
    (hreverse : ∀ x y, ENNReal.ofReal (D x y) =
      weylScaling E ξ (fun z => -f z) x y)
    (hpaths : (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric D ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 x) <
      ENNReal.ofReal (setDist D Q' (frontier Q))) :
    (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric E ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 x) <
      ENNReal.ofReal (setDist E Q' (frontier Q)) := by
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
  apply lt_of_le_of_lt ?_ (hpaths.trans_le hgapQ)
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  exact le_iSup_of_le x (le_iSup_of_le hx (internalMetric_le_of_ofReal_le horder _ _ _))

end HarmonicBalls
