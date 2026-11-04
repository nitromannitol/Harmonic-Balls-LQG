import HarmonicBalls.Proofs.Sec8.GaussianGerm

/-! # Interior field pairings and exterior radial circle averages -/

open MeasureTheory ProbabilityTheory Metric Set

namespace HarmonicBalls

/-- The covariance kernel averaged on a circle around an interior point is
constant inside the circle when the circle lies in the unit disk. -/
theorem circleAverage_wholePlaneCov_inside {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {x : ℂ} (hx : ‖x‖ ≤ s) :
    Real.circleAverage (fun y => wholePlaneCov x y) 0 s = -Real.log s := by
  have h : Real.circleAverage (fun y => wholePlaneCov x y) 0 s =
      Real.circleAverage (fun y => -Real.log ‖y - x‖) 0 s := by
    apply Real.circleAverage_congr_sphere
    intro y hy
    have hy' : ‖y‖ = s := by simpa [abs_of_pos hs] using hy
    simp only
    rw [wholePlaneCov_eq_neg_log (hx.trans hs1) (hy'.le.trans hs1), norm_sub_rev]
  rw [h]
  have h0 := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (c := 0) (a := x) hs.ne'
  have hratio : |s⁻¹ * ‖x‖| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hs.le) (norm_nonneg x))]
    exact (inv_mul_le_one₀ hs).2 hx
  rw [zero_sub, norm_neg, (Real.posLog_eq_zero_iff _).2 hratio, add_zero] at h0
  rw [Real.circleAverage_def] at h0 ⊢
  rw [intervalIntegral.integral_neg, smul_neg, h0]

/-- A zero-integral pairing supported in a disk has zero covariance with
concentric circle averages at any radius outside the disk and at most one. -/
theorem wholePlaneGFFCov_pairing_circle_of_integral_zero
    (φ : ℂ → ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hsupp : tsupport φ ⊆ closedBall (0 : ℂ) r) (hzero : ∫ x, φ x = 0) :
    wholePlaneGFFCov (.pairing φ) (.circle r 0) = 0 := by
  change (∫ x, φ x * Real.circleAverage (fun y => wholePlaneCov x y) 0 r) = 0
  calc
    _ = ∫ x, φ x * (-Real.log r) := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : φ x = 0
      · simp [hx]
      · have hmem : x ∈ tsupport φ := (subset_tsupport φ) (by simpa using hx)
        have hxnorm : ‖x‖ ≤ r := by simpa using hsupp hmem
        rw [circleAverage_wholePlaneCov_inside hr hr1 hxnorm]
    _ = (∫ x, φ x) * (-Real.log r) := integral_mul_const _ _
    _ = 0 := by rw [hzero, zero_mul]

/-- All zero-integral test-function pairings supported in a disk are jointly
independent of the concentric circle averages outside that disk and inside
the unit disk. -/
theorem IsWholePlaneGFF.indepFun_interiorPairings_exteriorCircleAverages
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {R : ℝ} (hR : 0 < R) :
    IndepFun
      (fun ω (φ : {φ : ℂ → ℝ // IsTestFunction (closedBall (0 : ℂ) R) φ ∧ ∫ x, φ x = 0}) =>
        hC ω φ.1)
      (fun ω (r : {r : ℝ // R ≤ r ∧ r ≤ 1}) => hcirc ω r.1 0) P := by
  let S := {φ : ℂ → ℝ // IsTestFunction (closedBall (0 : ℂ) R) φ ∧ ∫ x, φ x = 0}
  let T := {r : ℝ // R ≤ r ∧ r ≤ 1}
  let X : S → Ω → ℝ := fun φ ω => hC ω φ.1
  let Y : T → Ω → ℝ := fun r ω => hcirc ω r.1 0
  have htest (φ : S) : IsTestFunction Set.univ φ.1 :=
    ⟨φ.2.1.1, φ.2.1.2.1, subset_univ _⟩
  have hpos (r : T) : 0 < r.1 := hR.trans_le r.2.1
  let o : S ⊕ T → GFFObservable.Admissible := Sum.elim
    (fun φ => ⟨.pairing φ.1, htest φ⟩) (fun r => ⟨.circle r.1 0, hpos r⟩)
  have hg : IsGaussianProcess (Sum.elim X Y) P := by
    convert h.isGaussianProcess.comp_right o using 1
    funext q ω
    cases q <;> rfl
  apply hg.indepFun_of_covariance_eq_zero
  · exact fun φ => (h.measurable_pairing φ.1 (htest φ)).aemeasurable
  · exact fun r => (h.measurable_circle r.1 0 (hpos r)).aemeasurable
  · intro φ r
    have hs : tsupport φ.1 ⊆ closedBall (0 : ℂ) r.1 :=
      φ.2.1.2.2.trans (closedBall_subset_closedBall r.2.1)
    exact (h.covariance_eq (.pairing φ.1) (.circle r.1 0) (htest φ) (hpos r)).trans
      (wholePlaneGFFCov_pairing_circle_of_integral_zero φ.1 (hpos r) r.2.2 hs φ.2.2)

end HarmonicBalls
