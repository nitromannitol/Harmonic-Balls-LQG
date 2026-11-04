import HarmonicBalls.Proofs.Sec8.CircleDensityLocal

/-! # Logarithmic potential of a circle

Averaging the logarithmic kernel on a circle removes its point singularity.
The imported Section 8 argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

open MeasureTheory Set Metric Filter
open scoped Topology Real

namespace HarmonicBalls

/-- The logarithmic potential of a circle is the logarithm of the larger of
its radius and the distance to its center. -/
theorem circleAverage_log_norm_sub_eq_log_max {r : ℝ} (hr : 0 < r) (z x : ℂ) :
    Real.circleAverage (fun y => Real.log ‖y - x‖) z r =
      Real.log (max r ‖z - x‖) := by
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hr.ne']
  by_cases hx : ‖z - x‖ ≤ r
  · have hratio : |r⁻¹ * ‖z - x‖| ≤ 1 := by
      rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hr.le) (norm_nonneg _))]
      exact (inv_mul_le_one₀ hr).2 hx
    rw [(Real.posLog_eq_zero_iff _).2 hratio, add_zero, max_eq_left hx]
  · have hxr : r < ‖z - x‖ := lt_of_not_ge hx
    have hxn : ‖z - x‖ ≠ 0 := ne_of_gt (hr.trans hxr)
    have hratio : 1 ≤ |r⁻¹ * ‖z - x‖| := by
      rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hr.le) (norm_nonneg _))]
      exact (one_le_inv_mul₀ hr).2 hxr.le
    rw [Real.posLog_eq_log hratio, Real.log_mul (inv_ne_zero hr.ne') hxn,
      Real.log_inv, max_eq_right hxr.le]
    ring

/-- The averaged logarithmic kernel is continuous even when the point lies on
the circle. -/
theorem continuous_circleAverage_log_norm_sub {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Continuous (fun x : ℂ => Real.circleAverage (fun y => Real.log ‖y - x‖) z r) := by
  have heq : (fun x : ℂ => Real.circleAverage (fun y => Real.log ‖y - x‖) z r) =
      fun x => Real.log (max r ‖z - x‖) := by
    funext x
    exact circleAverage_log_norm_sub_eq_log_max hr z x
  rw [heq]
  exact (continuous_const.max ((continuous_const.sub continuous_id).norm)).log
    (fun x => ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _)))

/-- For a point inside or on a circle, its logarithmic potential is constant. -/
theorem circleAverage_log_norm_sub_of_dist_le {r : ℝ} (hr : 0 < r) (z x : ℂ)
    (hx : dist x z ≤ r) :
    Real.circleAverage (fun y => Real.log ‖y - x‖) z r = Real.log r := by
  rw [circleAverage_log_norm_sub_eq_log_max hr, max_eq_left]
  simpa [dist_eq_norm, norm_sub_rev] using hx

/-- The continuous normalization term in the whole-plane covariance kernel. -/
noncomputable def wholePlaneNormalization (x : ℂ) : ℝ := Real.log (max ‖x‖ 1)

theorem continuous_wholePlaneNormalization : Continuous wholePlaneNormalization := by
  unfold wholePlaneNormalization
  exact (continuous_norm.max continuous_const).log
    (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _)))

/-- Circle averaging the whole-plane covariance gives a continuous logarithmic
potential, with the diagonal ignored only inside the circle integral. -/
theorem circleAverage_wholePlaneCov_eq {r : ℝ} (hr : 0 < r) (z x : ℂ) :
    Real.circleAverage (fun y => wholePlaneCov x y) z r =
      wholePlaneNormalization x + Real.circleAverage wholePlaneNormalization z r -
        Real.log (max r ‖z - x‖) := by
  have hnorm : CircleIntegrable wholePlaneNormalization z r :=
    continuous_wholePlaneNormalization.continuousOn.circleIntegrable hr.le
  have heq : Real.circleAverage (fun y => wholePlaneCov x y) z r =
      Real.circleAverage (fun y => wholePlaneNormalization x + wholePlaneNormalization y -
        Real.log ‖y - x‖) z r := by
    apply Real.circleAverage_congr_codiscreteWithin _ hr.ne'
    filter_upwards [compl_singleton_mem_codiscreteWithin x] with y hyx
    have hne : y ≠ x := by simpa using hyx
    have hdist : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne.symm)
    have hx : max ‖x‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    have hy : max ‖y‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    rw [wholePlaneCov, wholePlaneNormalization, wholePlaneNormalization,
      Real.log_div (mul_ne_zero hx hy) hdist, Real.log_mul hx hy, norm_sub_rev]
  rw [heq]
  change Real.circleAverage (((fun _ : ℂ => wholePlaneNormalization x) +
    wholePlaneNormalization) - (fun y => Real.log ‖y - x‖)) z r = _
  rw [Real.circleAverage_sub
    ((circleIntegrable_const (wholePlaneNormalization x) z r).add hnorm)
    (circleIntegrable_log_norm_sub_const r),
    Real.circleAverage_add (circleIntegrable_const _ _ _) hnorm,
    Real.circleAverage_const, circleAverage_log_norm_sub_eq_log_max hr]

/-- The circle-averaged whole-plane covariance is continuous in the other point. -/
theorem continuous_circleAverage_wholePlaneCov {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Continuous (fun x : ℂ => Real.circleAverage (fun y => wholePlaneCov x y) z r) := by
  have heq : (fun x : ℂ => Real.circleAverage (fun y => wholePlaneCov x y) z r) =
      fun x => wholePlaneNormalization x + Real.circleAverage wholePlaneNormalization z r -
        Real.log (max r ‖z - x‖) := by
    funext x
    exact circleAverage_wholePlaneCov_eq hr z x
  rw [heq]
  exact (continuous_wholePlaneNormalization.add continuous_const).sub
    ((continuous_const.max ((continuous_const.sub continuous_id).norm)).log
      (fun x => ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _))))

/-- The excess of the circle's logarithmic potential is uniformly controlled
inside a slightly enlarged disk. -/
theorem circle_log_potential_excess_bound {r η : ℝ} (hr : 0 < r) (hη : 0 ≤ η)
    (z x : ℂ) (hx : x ∈ closedBall z (r + η)) :
    0 ≤ Real.log (max r ‖z - x‖) - Real.log r ∧
      Real.log (max r ‖z - x‖) - Real.log r ≤ Real.log (r + η) - Real.log r := by
  have hn : ‖z - x‖ ≤ r + η := by
    simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hx
  have hmax : max r ‖z - x‖ ≤ r + η := max_le (by linarith) hn
  constructor
  · linarith [Real.log_le_log hr (le_max_left r ‖z - x‖)]
  · linarith [Real.log_le_log (lt_of_lt_of_le hr (le_max_left r ‖z - x‖)) hmax]

/-- A compactly supported probability density in the enlarged disk has at most
the corresponding logarithmic-potential excess. -/
theorem integral_circle_log_potential_excess_bound {r η : ℝ} (hr : 0 < r) (hη : 0 ≤ η)
    (z : ℂ) (g : ℂ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgn : 0 ≤ g) (hgm : ∫ x, g x = 1)
    (hgs : tsupport g ⊆ closedBall z (r + η)) :
    0 ≤ ∫ x, g x * (Real.log (max r ‖z - x‖) - Real.log r) ∧
      (∫ x, g x * (Real.log (max r ‖z - x‖) - Real.log r)) ≤
        Real.log (r + η) - Real.log r := by
  let E : ℂ → ℝ := fun x => Real.log (max r ‖z - x‖) - Real.log r
  let b := Real.log (r + η) - Real.log r
  have hE : Continuous E := by
    apply Continuous.sub _ continuous_const
    exact (continuous_const.max ((continuous_const.sub continuous_id).norm)).log
      (fun x => ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _)))
  have hgi : Integrable g volume := hg.integrable_of_hasCompactSupport hgc
  have hEi : Integrable (fun x => g x * E x) volume :=
    (hg.mul hE).integrable_of_hasCompactSupport hgc.mul_right
  have hbi : Integrable (fun x => g x * b) volume := hgi.mul_const b
  have hnonneg : ∀ x, 0 ≤ g x * E x := by
    intro x
    apply mul_nonneg (hgn x)
    dsimp [E]
    linarith [Real.log_le_log hr (le_max_left r ‖z - x‖)]
  constructor
  · exact integral_nonneg hnonneg
  · calc
      (∫ x, g x * E x) ≤ ∫ x, g x * b := by
        apply integral_mono hEi hbi
        intro x
        by_cases hx : g x = 0
        · simp [hx]
        · apply mul_le_mul_of_nonneg_left _ (hgn x)
          exact (circle_log_potential_excess_bound hr hη z x
            (hgs (subset_closure hx))).2
      _ = b := by rw [integral_mul_const, hgm, one_mul]

/-- The same-center logarithmic potential excess of the normalized annular
densities tends to zero. -/
theorem circleDensity_log_potential_excess_tendsto_zero {r η : ℝ}
    (hr : 0 < r) (hη : 0 < η) (z : ℂ) :
    Tendsto (fun n : ℕ => ∫ x,
      ((∫ y, circleDensity r (circleDensityWidth r η n)
        (circleDensityWidth_pos hr hη n) 0 y)⁻¹ *
        circleDensity r (circleDensityWidth r η n) (circleDensityWidth_pos hr hη n) z x) *
      (Real.log (max r ‖z - x‖) - Real.log r)) atTop (𝓝 0) := by
  have hηlim : Tendsto (fun n : ℕ => η / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hradd : Tendsto (fun n : ℕ => r + η / ((n : ℝ) + 1)) atTop (𝓝 r) := by
    simpa using (tendsto_const_nhds (x := r)).add hηlim
  have hbound : Tendsto (fun n : ℕ => Real.log (r + η / ((n : ℝ) + 1)) - Real.log r)
      atTop (𝓝 0) := by
    simpa using ((Real.continuousAt_log hr.ne').tendsto.comp hradd).sub_const (Real.log r)
  apply squeeze_zero _ _ hbound
  all_goals
    intro n
    let δ := circleDensityWidth r η n
    let hδ := circleDensityWidth_pos hr hη n
    let g : ℂ → ℝ := fun x => (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x
    have hg : Continuous g := continuous_const.mul (circleDensity_contDiff r δ hδ z).continuous
    have hgc : HasCompactSupport g := (circleDensity_hasCompactSupport hr.le hδ z).mul_left
    have hgn : 0 ≤ g := fun x => mul_nonneg
      (inv_nonneg.mpr (circleDensity_integral_pos hr.le hδ 0).le)
      (circleDensity_nonneg r δ hδ z x)
    have hgm : ∫ x, g x = 1 := circleDensity_normalized_integral hr.le hδ z
    have hwidth : δ ≤ r * (η / ((n : ℝ) + 1)) := by
      dsimp [δ, circleDensityWidth]
      simp [div_eq_mul_inv, mul_assoc]
    have hgs : tsupport g ⊆ closedBall z (r + η / ((n : ℝ) + 1)) := by
      refine tsupport_mul_subset_right.trans ?_
      exact circleDensity_tsupport_subset_closedBall hr hδ hwidth z
    have h := integral_circle_log_potential_excess_bound hr (by positivity) z g hg hgc hgn hgm hgs
    first | exact h.1 | exact h.2

end HarmonicBalls
