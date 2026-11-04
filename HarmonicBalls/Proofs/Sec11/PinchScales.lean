import HarmonicBalls.Steps.Sec11.BadScales
import HarmonicBalls.Proofs.Sec11.PinchAnnulus

/-! # Pinch scales and the annulus comparison -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Dyadic balls centred away from two fixed points eventually exclude both. -/
theorem eventually_dyadic_balls_exclude (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ z) :
    ∀ᶠ n : ℕ in atTop,
      let r := (2 : ℝ)⁻¹ ^ n
      0 < r ∧ (0 : ℂ) ∉ closedBall z (10 * r) ∧ w ∉ ball z (10 * r) := by
  have hdist0 : 0 < dist (0 : ℂ) z := dist_pos.mpr (Ne.symm hz)
  have hdistw : 0 < dist w z := dist_pos.mpr hw
  have hε : 0 < min (dist (0 : ℂ) z) (dist w z) / 10 := by positivity
  have hp : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have he : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ)⁻¹ ^ n < min (dist (0 : ℂ) z) (dist w z) / 10 :=
    hp.eventually (Iio_mem_nhds hε)
  filter_upwards [he] with n hn
  have hr : 0 < (2 : ℝ)⁻¹ ^ n := by positivity
  refine ⟨hr, ?_, ?_⟩
  · change ¬ dist (0 : ℂ) z ≤ 10 * ((2 : ℝ)⁻¹ ^ n)
    have hh := min_le_left (dist (0 : ℂ) z) (dist w z)
    linarith
  · change ¬ dist w z < 10 * ((2 : ℝ)⁻¹ ^ n)
    have hh := min_le_right (dist (0 : ℂ) z) (dist w z)
    linarith

/-- For a point with arbitrarily many pinch scales, an annulus mass bound
valid at every sufficiently small scale excludes equality with a metric ball.
The exceptional set of scales may depend on the chosen centre. -/
theorem ne_metricBall_of_frequently_pinch_and_annulusMassBound
    (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q Λ : Set ℂ)
    (C u : ℝ) (w z : ℂ) (hconfig : IsPinchPointConfiguration U T Q' Q)
    (hD : IsEuclideanLengthMetric D) (hnonneg : ∀ x y, 0 ≤ D x y)
    (hz0 : z ≠ 0) (hzw : w ≠ z)
    (hz : z ∈ frontier (lqgMetricBall D w u))
    (hpinch : ∃ᶠ n : ℕ in atTop, pinchPointEvent μ D U T Q' Q C ((2 : ℝ)⁻¹ ^ n) z)
    (hbound : ∀ r : ℝ, 0 < r → (0 : ℂ) ∉ closedBall z (10 * r) →
      (annulus z (4 * r) (5 * r) ∩ Λᶜ).Nonempty →
      μ (annulus z r (2 * r) ∩ Λ) ≤
        ENNReal.ofReal C * annulusGreenPotentialSup μ z (3 * r) (6 * r)) :
    Λ ≠ lqgMetricBall D w u := by
  obtain ⟨n, hp, hr, h0, hw⟩ := (hpinch.and_eventually (eventually_dyadic_balls_exclude z w hz0 hzw)).exists
  exact ne_metricBall_of_pinchPointEvent_and_annulusMassBound μ D U T Q' Q Λ C
    ((2 : ℝ)⁻¹ ^ n) u w z hconfig hD hnonneg hp hr hw hz (hbound _ hr h0)

end HarmonicBalls
