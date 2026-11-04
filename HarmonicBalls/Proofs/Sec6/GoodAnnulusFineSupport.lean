import HarmonicBalls.Proofs.Sec6.AvoidanceIntegral
import HarmonicBalls.Proofs.Sec6.GoodAnnulusThreshold

/-! # Good annuli from fine support and a mean-value bound

This deterministic reduction connects the compact avoidance contradiction to
the good-annulus predicate. It isolates the Brownian mean-value estimate and
the instant-hitting property needed to obtain a positive mass threshold.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess Metric
open scoped ENNReal Topology

/-- Fine support and an integrated lower bound for compact avoidance imply the
existence of a positive good-annulus threshold. -/
theorem exists_goodAnnulus_threshold_of_fine_support
    (μ ν : Measure ℂ) [IsFiniteMeasure ν] {r b : ℝ} {z : ℂ}
    (hfinite : μ (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hx : ∀ᵐ x ∂ν, x ∈ annulus z (3 * r) (5 * r))
    (hfull : ∀ E : Set ℂ, MeasurableSet E → μ (annulus z (3 * r) (5 * r) \ E) = 0 →
      ∀ᵐ x ∂ν, ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω = 0)
    {d : ℝ≥0∞} (hd : 0 < d)
    (hmean : ∀ (K : Set ℂ), IsCompact K →
      ∀ u ∈ sphere z (4 * r), ENNReal.ofReal b < planarBrownianMotion u
        {ω | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} →
      d ≤ ∫⁻ x, planarBrownianMotion x
        {ω | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ∂ν) :
    ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus μ r z a b := by
  let A := annulus z (3 * r) (5 * r)
  have hopen : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  by_contra hnone
  have hbad (n : ℕ) : ¬ IsGoodAnnulus μ r z ((1 / 2 : ℝ) ^ n) b := by
    intro hgood
    exact hnone ⟨_, by positivity, hgood⟩
  have hex (n : ℕ) : ∃ Y : Set ℂ, MeasurableSet Y ∧ Y ⊆ A ∧
      μ Y ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * μ A ∧
      ∃ u ∈ sphere z (4 * r), ENNReal.ofReal b < planarBrownianMotion u
        {ω | ContinuousPath.exitTime A ω ≤ ContinuousPath.exitTime Y ω} := by
    have h := hbad n
    simp only [IsGoodAnnulus] at h
    push Not at h
    exact h
  choose Y hY hYA hsmall u hu hprob using hex
  have hsmall' (n : ℕ) : μ (Y n) ≤ (2⁻¹ : ℝ≥0∞) ^ n * μ A := by
    have heq : ENNReal.ofReal ((1 / 2 : ℝ) ^ n) = (2⁻¹ : ℝ≥0∞) ^ n := by
      rw [ENNReal.ofReal_pow (by norm_num), one_div,
        ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    simpa only [heq] using hsmall n
  apply not_uniform_avoidance_of_dyadic_exceptions hopen μ ν hopen.measurableSet hfinite hx
    hfull Y hY hsmall' hd
  intro n K hK hKY
  apply hmean K hK (u n) (hu n)
  apply (hprob n).trans_le
  apply measure_mono
  apply stay_subset_avoid_before_exit
  exact disjoint_left.mpr (fun x hxK hxY => (hKY hxK).2 hxY)

end HarmonicBalls.Section6
