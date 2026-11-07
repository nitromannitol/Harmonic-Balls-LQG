import HarmonicBalls.Proofs.Sec11.CorrectedPinchBufferedWeight
import HarmonicBalls.Proofs.Sec11.CorrectedPinchBoundaryScaling

/-! Lower boundary-distance estimates for the first pinch-event Weyl shift. -/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- A buffered obstacle plateau amplifies the distance from the inner
obstacle set to the obstacle boundary. -/
theorem IsPinchPointProofConfiguration.obstacle_boundary_weyl_lower_bound
    {U V W T Q' Q : Set ℂ} {δ ξ a : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) {f : ℂ → ℝ}
    (hf : ∀ x ∈ thickening (δ / 2) Q, f x = a)
    (hreverse : ∀ x y, ENNReal.ofReal (D x y) =
      weylScaling E ξ (fun z => -f z) x y) :
    ENNReal.ofReal (Real.exp (ξ * a)) *
        ENNReal.ofReal (setDist D Q' (frontier Q)) ≤
      ENNReal.ofReal (setDist E Q' (frontier Q)) := by
  have hδ : 0 < δ := h.δ₀_mem.1
  have hQne : Q ≠ univ := by
    intro heq
    have hz : (0 : ℂ) ∈ Q := by rw [heq]; exact mem_univ _
    exact (h.Q_subset hz).1.2 (by simp)
  have hfrontQ : (frontier Q).Nonempty :=
    nonempty_frontier_iff.mpr ⟨h.isConnected_Q.nonempty, hQne⟩
  apply ofReal_mul_setDist_boundary_le_of_inverse_weylScaling hD hE h.isOpen_Q
    isOpen_thickening (subset_closure.trans h.closure_Q'_subset)
    (closure_subset_thickening (by linarith : 0 < δ / 2) Q)
    h.isConnected_Q'.nonempty hfrontQ ?_ hreverse
  intro x hx
  rw [hf x hx]

/-- A buffered root plateau amplifies the distance to the sphere of radius
half the cutoff radius. -/
theorem IsPinchPointProofConfiguration.root_boundary_weyl_lower_bound
    {U V W T Q' Q : Set ℂ} {δ ξ b : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) {f : ℂ → ℝ}
    (hf : ∀ x ∈ ball 0 (3 * δ / 4), f x = b)
    (hreverse : ∀ x y, ENNReal.ofReal (D x y) =
      weylScaling E ξ (fun z => -f z) x y) :
    ENNReal.ofReal (Real.exp (ξ * b)) *
        ENNReal.ofReal (setDist D {0} (sphere 0 (δ / 2))) ≤
      ENNReal.ofReal (setDist E {0} (sphere 0 (δ / 2))) := by
  have hδ : 0 < δ := h.δ₀_mem.1
  have hδ2 : 0 < δ / 2 := by linarith
  have hballcl : closure (ball (0 : ℂ) (δ / 2)) ⊆ ball 0 (3 * δ / 4) := by
    rw [closure_ball 0 hδ2.ne']
    intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball]
    linarith
  have hfront : (frontier (ball (0 : ℂ) (δ / 2))).Nonempty := by
    rw [frontier_ball (0 : ℂ) hδ2.ne']
    exact NormedSpace.sphere_nonempty.mpr hδ2.le
  have hg := ofReal_mul_setDist_boundary_le_of_inverse_weylScaling hD hE isOpen_ball
    isOpen_ball (singleton_subset_iff.mpr (mem_ball_self hδ2)) hballcl
    (singleton_nonempty 0) hfront (L := ξ * b) (by
      intro x hx
      rw [hf x hx]) hreverse
  simpa only [frontier_ball (0 : ℂ) hδ2.ne'] using hg

#print axioms IsPinchPointProofConfiguration.obstacle_boundary_weyl_lower_bound
#print axioms IsPinchPointProofConfiguration.root_boundary_weyl_lower_bound

end HarmonicBalls
