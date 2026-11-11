import HarmonicBalls.FirstPass.S11j.Geometry
import HarmonicBalls.Proofs.Sec11.CorrectedPinchOpenFirstShift

/-!
# Section 11: the deterministic shift of the faithful Lemma 11.15

Wrapper of the deterministic core shift `IsPinchPointProofConfiguration.exists_uniform_open_first_event_shift`
(`Proofs/Sec11/CorrectedPinchOpenFirstShift.lean:14`) for the buffered pinch geometry. The shift vanishes off
`thickening δ Q ∪ ball 0 δ`, so it vanishes on the unit circle (paper line 3659-3696; the unit circle lies in the annulus
`4 < |z| < 5` complement of `thickening δ Q`, since `δ < 1/1000`). The vanishing on the unit circle is the condition that
makes the shift a Cameron-Martin direction (zero circle average).
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- The unit circle avoids `thickening δ Q ∪ ball 0 δ` in a buffered pinch geometry. -/
theorem unit_circle_not_mem_support {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsBufferedPinchGeometry U V W T Q' Q δ) (hδ : 0 < δ) (z : ℂ) (hz : ‖z‖ = 1) :
    z ∉ thickening δ Q ∪ ball (0 : ℂ) δ := by
  intro hmem
  rcases hmem with hmem | hmem
  · rw [Metric.mem_thickening_iff] at hmem
    obtain ⟨q, hq, hd⟩ := hmem
    obtain ⟨⟨-, hq4⟩, -⟩ := h.closure_Q_subset (subset_closure hq)
    have h4 : 4 < ‖q‖ := by
      have : ¬ (dist q 0 ≤ 4) := fun hle => hq4 (mem_closedBall.2 hle)
      rw [dist_zero_right] at this
      exact not_le.1 this
    have hd' : ‖q - z‖ < δ := by
      rw [← dist_eq_norm, dist_comm]
      exact hd
    have hsplit : q = z + (q - z) := by ring
    have htri : ‖q‖ ≤ ‖z‖ + ‖q - z‖ := by
      calc ‖q‖ = ‖z + (q - z)‖ := by rw [← hsplit]
        _ ≤ ‖z‖ + ‖q - z‖ := norm_add_le _ _
    have hδ1 := h.delta_lt
    linarith
  · rw [mem_ball, dist_zero_right] at hmem
    have hδ1 := h.delta_lt
    linarith

/-- The deterministic core shift for a buffered pinch geometry: a smooth nonnegative compactly supported `f` vanishing
on the unit circle, for which the first pinch event holds for every admissible pair of metrics `E = e^{ξ f} D`,
`D = e^{-ξ f} E` (core lemma, with the unit-circle condition derived from the support condition). -/
theorem exists_core_shift {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsBufferedPinchGeometry U V W T Q' Q δ) (hU : U.Nonempty) (hδ : 0 < δ) (hξ : 0 < ξ)
    (n m k l : ℕ) (hn : 0 < n) (hk : 0 < k) :
    ∃ f : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ (∀ x, 0 ≤ f x) ∧
      (∀ z : ℂ, ‖z‖ = 1 → f z = 0) ∧
      ∀ D E : ℂ → ℂ → ℝ, IsEuclideanLengthMetric D → IsEuclideanLengthMetric E →
        (∀ x y, 0 ≤ E x y) →
        (∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y) →
        (∀ x y, ENNReal.ofReal (D x y) = weylScaling E ξ (fun z => -f z) x y) →
        (n : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (setDist D Q' (frontier Q)) →
        (⨆ y ∈ sphere (0 : ℂ) 5, internalMetric D
          (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0 y) ≤ m →
        (k : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (setDist D {0} (sphere 0 (δ / 2))) →
        internalDiam D δ (T \ thickening (3 * δ) W) ≤ l →
        pinchFirstEvent E W T Q' Q δ ∧
        (⨆ y ∈ sphere (0 : ℂ) 5, internalMetric E
          (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0 y) <
          ENNReal.ofReal (setDist E Q' (frontier Q)) := by
  obtain ⟨f, hsm, hcomp, hnonneg, hsupp, hcore⟩ :=
    (h.toPinchPointProofConfiguration hU).exists_uniform_open_first_event_shift hξ n m k l hn hk
  exact ⟨f, hsm, hcomp, hnonneg, fun z hz => hsupp z (unit_circle_not_mem_support h hδ z hz), hcore⟩

end HarmonicBalls
