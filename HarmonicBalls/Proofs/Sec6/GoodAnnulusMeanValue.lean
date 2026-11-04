import HarmonicBalls.Proofs.Sec6.GoodAnnulusFineSupport

/-! # Geometry of the good-annulus mean-value bound -/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess Metric
open scoped ENNReal Topology

/-- Every ball of radius `r/4` centred on the middle circle is contained in
the concentric annulus of radii `15r/4` and `17r/4`. -/
theorem middleCircle_ball_subset_innerAnnulus {z u : ℂ} {r : ℝ} (_hr : 0 < r)
    (hu : u ∈ sphere z (4 * r)) :
    ball u (r / 4) ⊆ annulus z (15 * r / 4) (17 * r / 4) := by
  intro x hx
  have hdist : dist u z = 4 * r := by simpa only [mem_sphere] using hu
  have hxu : dist x u < r / 4 := by simpa only [mem_ball] using hx
  have hupper := dist_triangle x u z
  have hlower := dist_triangle u x z
  have hsymm : dist u x = dist x u := dist_comm _ _
  change x ∈ ball z (17 * r / 4) ∧ x ∉ closedBall z (15 * r / 4)
  simp only [mem_ball, mem_closedBall, not_le]
  constructor <;> linarith

/-- The inner annulus is contained in the original good annulus. -/
theorem innerAnnulus_subset_goodAnnulus (z : ℂ) {r : ℝ} (hr : 0 < r) :
    annulus z (15 * r / 4) (17 * r / 4) ⊆ annulus z (3 * r) (5 * r) := by
  intro x hx
  change x ∈ ball z (17 * r / 4) ∧ x ∉ closedBall z (15 * r / 4) at hx
  change x ∈ ball z (5 * r) ∧ x ∉ closedBall z (3 * r)
  simp only [mem_ball, mem_closedBall, not_le] at hx ⊢
  constructor <;> linarith

/-- A ball submean bound for compact avoidance gives the uniform integrated
lower estimate required in the good-annulus reduction. -/
theorem integrated_avoidance_lower_of_ball_submean
    {z : ℂ} {r b : ℝ} (hr : 0 < r) (hb : 0 < b) {C : ℝ≥0∞}
    (hC0 : C ≠ 0) (hCtop : C ≠ ∞)
    (hsubmean : ∀ K : Set ℂ, IsCompact K → ∀ u ∈ sphere z (4 * r),
      planarBrownianMotion u
        {ω | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ≤
      C * ∫⁻ x in ball u (r / 4), planarBrownianMotion x
        {ω | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ∂volume) :
    ∃ d : ℝ≥0∞, 0 < d ∧ ∀ (K : Set ℂ), IsCompact K →
      ∀ u ∈ sphere z (4 * r), ENNReal.ofReal b < planarBrownianMotion u
        {ω | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} →
      d ≤ ∫⁻ x in annulus z (15 * r / 4) (17 * r / 4), planarBrownianMotion x
        {ω | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ∂volume := by
  refine ⟨ENNReal.ofReal b / C, ENNReal.div_pos (ne_of_gt (ENNReal.ofReal_pos.mpr hb)) hCtop, ?_⟩
  intro K hK u hu huavoid
  apply (ENNReal.div_le_iff_le_mul (Or.inl hC0) (Or.inl hCtop)).2
  rw [mul_comm]
  calc
    ENNReal.ofReal b ≤ planarBrownianMotion u
        {ω | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} := huavoid.le
    _ ≤ C * ∫⁻ x in ball u (r / 4), planarBrownianMotion x
        {ω | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ∂volume := hsubmean K hK u hu
    _ ≤ C * ∫⁻ x in annulus z (15 * r / 4) (17 * r / 4), planarBrownianMotion x
        {ω | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ∂volume := by
      gcongr
      exact middleCircle_ball_subset_innerAnnulus hr hu

/-- A ball submean estimate and instant hitting from almost every point in the
inner annulus imply a positive good-annulus threshold. -/
theorem exists_goodAnnulus_threshold_of_ball_submean
    (μ : Measure ℂ) {z : ℂ} {r b : ℝ} (hr : 0 < r) (hb : 0 < b)
    (hfinite : μ (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hfull : ∀ E : Set ℂ, MeasurableSet E → μ (annulus z (3 * r) (5 * r) \ E) = 0 →
      ∀ᵐ x ∂(volume.restrict (annulus z (15 * r / 4) (17 * r / 4))),
        ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω = 0)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ∞)
    (hsubmean : ∀ K : Set ℂ, IsCompact K → ∀ u ∈ sphere z (4 * r),
      planarBrownianMotion u
        {ω | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ≤
      C * ∫⁻ x in ball u (r / 4), planarBrownianMotion x
        {ω | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ∂volume) :
    ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus μ r z a b := by
  let A := annulus z (15 * r / 4) (17 * r / 4)
  let ν : Measure ℂ := volume.restrict A
  have hA : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  have hAfinite : volume A ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ball_lt_top (μ := volume)).ne (measure_mono sdiff_subset)
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hAfinite
  have hx : ∀ᵐ x ∂ν, x ∈ annulus z (3 * r) (5 * r) :=
    (ae_restrict_mem hA.measurableSet).mono (innerAnnulus_subset_goodAnnulus z hr)
  obtain ⟨d, hd, hmean⟩ := integrated_avoidance_lower_of_ball_submean hr hb hC0 hCtop hsubmean
  exact exists_goodAnnulus_threshold_of_fine_support μ ν hfinite hx hfull hd hmean

end HarmonicBalls.Section6
