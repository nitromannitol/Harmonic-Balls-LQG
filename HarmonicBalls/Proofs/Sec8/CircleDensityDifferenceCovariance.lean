import HarmonicBalls.Proofs.Sec8.CircleDensityContinuousLimit

/-! # Circle covariances of annular differences

The circle-pairing terms in the local approximation error converge to the
corresponding circle-circle terms. The imported Section 8 argument uses Leonardo
Bonanno's LatticeProb formalization of the ergodic theorem.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter Real
open scoped Topology ProbabilityTheory

namespace HarmonicBalls

/-- The covariance of an annular density difference with a circle converges
to the difference of circle covariances. -/
theorem circleDensityDifference_circle_covariance_tendsto {r η s : ℝ}
    (hr : 0 < r) (hη : 0 < η) (hs : 0 < s) (z w : ℂ) :
    Tendsto (fun n => wholePlaneGFFCov (.pairing (circleDensityDifference r η hr hη z n))
      (.circle s w)) atTop
      (𝓝 (wholePlaneGFFCov (.circle r z) (.circle s w) -
        wholePlaneGFFCov (.circle r 0) (.circle s w))) := by
  have ht := (circleDensity_circle_covariance_tendsto hr hη hs z w).sub
    (circleDensity_circle_covariance_tendsto hr hη hs 0 w)
  apply ht.congr'
  filter_upwards with n
  let δ := circleDensityWidth r η n
  let hδ := circleDensityWidth_pos hr hη n
  let m : ℝ := (∫ y, circleDensity r δ hδ 0 y)⁻¹
  let f : ℂ → ℝ := fun x => Real.circleAverage (fun y => wholePlaneCov x y) w s
  have hf : Continuous f := continuous_circleAverage_wholePlaneCov hs w
  have hi (v : ℂ) : Integrable (fun x => m * circleDensity r δ hδ v x * f x) := by
    apply ((continuous_const.mul (circleDensity_contDiff r δ hδ v).continuous).mul hf).integrable_of_hasCompactSupport
    exact (circleDensity_hasCompactSupport hr.le hδ v).mul_left.mul_right
  symm
  change (∫ x, (m * circleDensity r δ hδ z x - m * circleDensity r δ hδ 0 x) * f x) =
    (∫ x, m * circleDensity r δ hδ z x * f x) -
      ∫ x, m * circleDensity r δ hδ 0 x * f x
  simp_rw [sub_mul]
  exact integral_sub (hi z) (hi 0)

/-- Once the self-covariance of the annular difference converges, all
remaining terms in the local circle approximation error cancel. -/
theorem IsWholePlaneGFF.circleDensityDifference_error_tendsto_of_self
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {r η : ℝ}
    (hr : 0 < r) (hη : 0 < η) (z : ℂ)
    (hself : Tendsto (fun n => wholePlaneGFFCov
      (.pairing (circleDensityDifference r η hr hη z n))
      (.pairing (circleDensityDifference r η hr hη z n))) atTop
      (𝓝 (wholePlaneGFFCov (.circle r z) (.circle r z) +
        wholePlaneGFFCov (.circle r 0) (.circle r 0) -
        2 * wholePlaneGFFCov (.circle r z) (.circle r 0)))) :
    Tendsto (fun n =>
      wholePlaneGFFCov (.pairing (circleDensityDifference r η hr hη z n))
        (.pairing (circleDensityDifference r η hr hη z n)) +
      wholePlaneGFFCov (.circle r z) (.circle r z) +
      wholePlaneGFFCov (.circle r 0) (.circle r 0) -
      2 * wholePlaneGFFCov (.circle r z) (.circle r 0) -
      2 * wholePlaneGFFCov (.pairing (circleDensityDifference r η hr hη z n)) (.circle r z) +
      2 * wholePlaneGFFCov (.pairing (circleDensityDifference r η hr hη z n)) (.circle r 0))
      atTop (𝓝 0) := by
  have hz := circleDensityDifference_circle_covariance_tendsto hr hη hr z z
  have h0 := circleDensityDifference_circle_covariance_tendsto hr hη hr z 0
  have hsym : wholePlaneGFFCov (.circle r 0) (.circle r z) =
      wholePlaneGFFCov (.circle r z) (.circle r 0) := by
    have h₁ := hGFF.covariance_eq (.circle r 0) (.circle r z) hr hr
    have h₂ := hGFF.covariance_eq (.circle r z) (.circle r 0) hr hr
    simp only [GFFObservable.eval] at h₁ h₂
    rw [← h₁, ← h₂, covariance_comm]
  have hlimit := (((((hself.add (tendsto_const_nhds
    (x := wholePlaneGFFCov (.circle r z) (.circle r z)))).add (tendsto_const_nhds
    (x := wholePlaneGFFCov (.circle r 0) (.circle r 0)))).sub
    ((tendsto_const_nhds (x := (2 : ℝ))).mul (tendsto_const_nhds
      (x := wholePlaneGFFCov (.circle r z) (.circle r 0))))).sub
    ((tendsto_const_nhds (x := (2 : ℝ))).mul hz)).add
    ((tendsto_const_nhds (x := (2 : ℝ))).mul h0))
  have heq : (wholePlaneGFFCov (.circle r z) (.circle r z) +
      wholePlaneGFFCov (.circle r 0) (.circle r 0) -
      2 * wholePlaneGFFCov (.circle r z) (.circle r 0)) +
      wholePlaneGFFCov (.circle r z) (.circle r z) +
      wholePlaneGFFCov (.circle r 0) (.circle r 0) -
      2 * wholePlaneGFFCov (.circle r z) (.circle r 0) -
      2 * (wholePlaneGFFCov (.circle r z) (.circle r z) -
        wholePlaneGFFCov (.circle r 0) (.circle r z)) +
      2 * (wholePlaneGFFCov (.circle r z) (.circle r 0) -
        wholePlaneGFFCov (.circle r 0) (.circle r 0)) = 0 := by
    rw [hsym]
    ring
  simpa only [heq] using hlimit

end HarmonicBalls
