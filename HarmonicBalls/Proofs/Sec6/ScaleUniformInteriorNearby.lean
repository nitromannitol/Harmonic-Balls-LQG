import HarmonicBalls.Proofs.Sec6.ScaledInteriorCoreReturn
import HarmonicBalls.Proofs.Sec6.AnnulusMassSandwich
import HarmonicBalls.Proofs.Sec6.CollarAvoidanceComparison

/-! # Nearby-annulus estimates for arbitrary interior margins -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set MarkovProcess
open scoped ENNReal NNReal

/-- Uniform Brownian return bound for nearby centres at every scale. -/
theorem exists_scale_uniform_nearby_core_return_of_margin
    {κ : ℝ} (hκ : 0 < κ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ r : ℝ, 0 < r → ∀ z w : ℂ, dist w z < η*r →
      ∀ x ∈ sphere (0 : ℂ) 4,
      planarBrownianMotion (r • x + w) {ω | ∃ t : ℝ≥0,
        ContinuousPath.exitTime (annulus w (3*r) (5*r)) ω ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < ContinuousPath.exitTime (annulus z (3*r) (5*r)) ω ∧
        r * (3 + κ) ≤ dist (ω t) z ∧ dist (ω t) z ≤ r * (5 - κ)} < ε := by
  obtain ⟨η₀, hη₀, hbound⟩ := exists_scale_and_centre_uniform_radial_core_return_of_interior
    (s := 3 + κ / 2) (S := 5 - κ / 2) (by linarith) (by linarith) hε
  let η := min η₀ (κ / 2)
  have hη : 0 < η := lt_min hη₀ (by linarith)
  refine ⟨η, hη, ?_⟩
  intro r hr z w hw x hx
  have hdist : dist z w < η₀*r := by
    rw [dist_comm]
    exact hw.trans_le (mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le)
  have hquarter : dist w z < r * (κ / 2) := by
    have h := hw.trans_le (mul_le_mul_of_nonneg_right (min_le_right η₀ (κ / 2)) hr.le)
    nlinarith
  have hinner : annulus w (r * (3 + η₀)) (r * (5 - η₀)) ⊆ annulus w (3*r) (5*r) := by
    have h := (annulus_nearby_center_sandwich (z := w) (w := w)
      (r := 3*r) (R := 5*r) (ε := η₀*r) (by simpa using mul_pos hη₀ hr)).1
    convert h using 1; ring_nf
  have houter : annulus z (3*r) (5*r) ⊆ annulus w (r * (3 - η₀)) (r * (5 + η₀)) := by
    have h := (annulus_nearby_center_sandwich (z := w) (w := z)
      (r := 3*r) (R := 5*r) hdist).2
    convert h using 1; ring_nf
  apply lt_of_le_of_lt ?_ (hbound r hr w x hx)
  apply measure_mono
  rintro ω ⟨t, htB, htA, hlow, hupp⟩
  refine ⟨t, (ContinuousPath.exitTime_mono hinner ω).trans htB,
    htA.trans_le (ContinuousPath.exitTime_mono houter ω), ?_, ?_⟩
  · have h := dist_triangle (ω t) w z
    nlinarith
  · have h := dist_triangle (ω t) z w
    rw [dist_comm z w] at h
    nlinarith


/-- Nearby-annulus avoidance comparison, uniform in scale and centre. The
    comparison witness includes the complement of a interior core with any prescribed positive margin. -/
theorem exists_scale_uniform_nearby_avoidance_comparison_of_margin
    {κ : ℝ} (hκ : 0 < κ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ r : ℝ, 0 < r → ∀ z w : ℂ, dist w z < η*r →
      ∀ x ∈ sphere (0 : ℂ) 4, ∀ Y : Set ℂ,
      planarBrownianMotion (r • x + w) {ω |
        ContinuousPath.exitTime (annulus w (3*r) (5*r)) ω ≤
          ContinuousPath.exitTime Y ω} ≤
      planarBrownianMotion (r • x + w) {ω |
        ContinuousPath.exitTime (annulus z (3*r) (5*r)) ω ≤
          ContinuousPath.exitTime
            ((annulus z (3*r) (5*r) ∩ Y) ∪
              (annulus z (3*r) (5*r) \ {q | r * (3 + κ) ≤ dist q z ∧
                dist q z ≤ r * (5 - κ)})) ω} + ε := by
  obtain ⟨η, hη, hreturn⟩ := exists_scale_uniform_nearby_core_return_of_margin hκ hε
  refine ⟨η, hη, ?_⟩
  intro r hr z w hw x hx Y
  apply (stay_probability_le_collar_avoidance_add_return
    (planarBrownianMotion (r • x + w)) (annulus z (3*r) (5*r))
    (annulus w (3*r) (5*r))
    {q | r * (3 + κ) ≤ dist q z ∧ dist q z ≤ r * (5 - κ)} Y).trans
  exact add_le_add le_rfl (le_of_lt (hreturn r hr z w hw x hx))


end HarmonicBalls.Section6
