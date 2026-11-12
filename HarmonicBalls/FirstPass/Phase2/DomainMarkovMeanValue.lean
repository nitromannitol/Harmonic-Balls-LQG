import HarmonicBalls.FirstPass.Phase2.DomainMarkovOuterPotential

/-!
# Mean value property of the covariance potential

For a test function `ρ` and a closed disk `B̄_r(z)` disjoint from `tsupport ρ`, the average over `∂B_r(z)` of the
logarithmic potential of `ρ` equals its value at the centre (the logarithmic potential is harmonic off the support;
here the identity is read off from the circle average of `log |· - y|`, which is `log |z - y|` for `|z - y| ≥ r`).
For a mean-zero `ρ` the covariance potential `outerPotential ρ` is the logarithmic potential plus a constant, so
the same holds for it, and the covariance of the circle average `h_r(z)` of the whole-plane GFF with the pairing
`(h, ρ)` is `outerPotential ρ z`.

## Main results

* `circleAverage_logPot_eq_of_disjoint`: mean value property of the logarithmic potential;
* `circleAverage_outerPotential_eq_of_disjoint`: mean value property of the covariance potential;
* `IsWholePlaneGFF.covariance_circle_pairing_eq_outerPotential`: `Cov(h_r(z), (h, ρ)) = outerPotential ρ z`.
-/

open MeasureTheory ProbabilityTheory

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Outside the open disk `B_r(z)`, the circle average of `log |· - u|` over `∂B_r(z)` is `log |z - u|`. -/
theorem circLog_eq_log_norm_of_le {z u : ℂ} {r : ℝ} (hr : 0 < r) (hu : r ≤ ‖z - u‖) :
    LQGMetric.CircleAvg.circLog z r u = Real.log ‖z - u‖ := by
  have hzu : 0 < ‖z - u‖ := hr.trans_le hu
  have h1 : 1 ≤ |r⁻¹ * ‖z - u‖| := by
    rw [abs_of_nonneg (by positivity)]
    exact (one_le_inv_mul₀ hr).mpr hu
  rw [LQGMetric.CircleAvg.circLog_eq hr.ne' z u, Real.posLog_eq_log h1,
    Real.log_mul (inv_ne_zero hr.ne') hzu.ne', Real.log_inv]
  ring

/-- **Mean value property of the logarithmic potential.** If the closed disk `B̄_r(z)` does not meet the support
of the test function `ρ`, the average of the logarithmic potential of `ρ` over `∂B_r(z)` is its value at `z`. -/
theorem circleAverage_logPot_eq_of_disjoint {ρ : ℂ → ℝ} (hρ : IsTestFunction Set.univ ρ) {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hdisj : Disjoint (Metric.closedBall z r) (tsupport ρ)) :
    Real.circleAverage (LQGMetric.CircleAvg.logPot ρ) z r = LQGMetric.CircleAvg.logPot ρ z := by
  refine (circleAverage_logPot_circle (⟨ρ, hρ.1, hρ.2.1, Set.subset_univ _⟩ : LQGMetric.TestC) z hr).trans ?_
  unfold LQGMetric.CircleAvg.logPot
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change -(ρ y * LQGMetric.CircleAvg.circLog z r y) = -Real.log ‖z - y‖ * ρ y
  by_cases hy : ρ y = 0
  · simp [hy]
  · have hyt : y ∈ tsupport ρ := subset_tsupport _ hy
    have hyb : y ∉ Metric.closedBall z r := fun h => hdisj.ne_of_mem h hyt rfl
    rw [Metric.mem_closedBall, not_le, dist_eq_norm] at hyb
    rw [circLog_eq_log_norm_of_le hr (by rw [norm_sub_rev]; exact hyb.le)]
    ring

/-- **Mean value property of the covariance potential.** If the closed disk `B̄_r(z)` does not meet the support of
the mean-zero test function `ρ`, the average of `outerPotential ρ` over `∂B_r(z)` is `outerPotential ρ z`. -/
theorem circleAverage_outerPotential_eq_of_disjoint {ρ : ℂ → ℝ} (hρ : IsTestFunction Set.univ ρ)
    (h0 : ∫ y, ρ y = 0) {z : ℂ} {r : ℝ} (hr : 0 < r) (hdisj : Disjoint (Metric.closedBall z r) (tsupport ρ)) :
    Real.circleAverage (outerPotential ρ) z r = outerPotential ρ z := by
  have hpot : outerPotential ρ = fun x => LQGMetric.CircleAvg.logPot ρ x +
      ∫ y, ρ y * LQGMetric.CircleAvg.circLog 0 1 y :=
    funext (outerPotential_eq_logPot_add_of_integral_eq_zero hρ h0)
  have hcont : Continuous (LQGMetric.CircleAvg.logPot ρ) :=
    (LQGMetric.MarkovGermVer.contDiff_logPot ⟨ρ, hρ.1, hρ.2.1, Set.subset_univ _⟩).continuous
  rw [hpot, Real.circleAverage_fun_add (hcont.continuousOn.circleIntegrable hr.le)
    (circleIntegrable_const (∫ y, ρ y * LQGMetric.CircleAvg.circLog 0 1 y) z r),
    Real.circleAverage_const, circleAverage_logPot_eq_of_disjoint hρ hr hdisj]

/-- **Covariance of a circle average with an outer pairing.** For a mean-zero test function `ρ` whose support does
not meet the closed disk `B̄_r(z)`, the covariance of the circle average `h_r(z)` of the whole-plane GFF with the
pairing `(h, ρ)` is the covariance potential `outerPotential ρ z`. -/
theorem IsWholePlaneGFF.covariance_circle_pairing_eq_outerPotential (hh : IsWholePlaneGFF P hC hcirc)
    {ρ : ℂ → ℝ} (hρ : IsTestFunction Set.univ ρ) (h0 : ∫ y, ρ y = 0) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hdisj : Disjoint (Metric.closedBall z r) (tsupport ρ)) :
    cov[fun s => hcirc s r z, fun s => hC s ρ; P] = outerPotential ρ z :=
  (hh.covariance_eq (.circle r z) (.pairing ρ) hr hρ).trans
    (circleAverage_outerPotential_eq_of_disjoint hρ h0 hr hdisj)

end HarmonicBalls
