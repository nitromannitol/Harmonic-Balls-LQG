import HarmonicBalls.Proofs.Sec8.CirclePairingCovariance

/-! # Smooth annular approximations

Smooth radial bumps around a circle have positive, translation-invariant mass.
The imported Section 8 argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

open MeasureTheory Set Metric
open scoped ContDiff

namespace HarmonicBalls

/-- A smooth bump in squared radius, supported in an annulus around the circle. -/
noncomputable def circleRadiusBump (r δ : ℝ) (hδ : 0 < δ) : ContDiffBump (r ^ 2) where
  rIn := δ / 2
  rOut := δ
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

/-- The annular bump centered at `z`. -/
noncomputable def circleDensity (r δ : ℝ) (hδ : 0 < δ) (z x : ℂ) : ℝ :=
  circleRadiusBump r δ hδ (‖x - z‖ ^ 2)

/-- The annular density is smooth, including on the diagonal. -/
theorem circleDensity_contDiff (r δ : ℝ) (hδ : 0 < δ) (z : ℂ) :
    ContDiff ℝ ∞ (circleDensity r δ hδ z) := by
  exact (circleRadiusBump r δ hδ).contDiff.comp
    ((contDiff_id.sub contDiff_const).norm_sq ℝ)

/-- The support lies in the prescribed squared-radius annulus. -/
theorem circleDensity_support (r δ : ℝ) (hδ : 0 < δ) (z x : ℂ)
    (hx : x ∈ Function.support (circleDensity r δ hδ z)) :
    |‖x - z‖ ^ 2 - r ^ 2| < δ := by
  have h : ‖x - z‖ ^ 2 ∈ ball (r ^ 2) δ := by
    have hm : ‖x - z‖ ^ 2 ∈ Function.support (circleRadiusBump r δ hδ) := hx
    rw [(circleRadiusBump r δ hδ).support_eq] at hm
    exact hm
  simpa [mem_ball, Real.dist_eq] using h

/-- Every such density has compact support. -/
theorem circleDensity_hasCompactSupport {r : ℝ} (hr : 0 ≤ r) {δ : ℝ} (hδ : 0 < δ)
    (z : ℂ) : HasCompactSupport (circleDensity r δ hδ z) := by
  have hsub : tsupport (circleDensity r δ hδ z) ⊆ closedBall z (r + δ + 1) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    have h := circleDensity_support r δ hδ z x hx
    have hn : 0 ≤ ‖x - z‖ := norm_nonneg _
    rw [abs_lt] at h
    rw [mem_closedBall, dist_eq_norm]
    nlinarith [sq_nonneg (‖x - z‖ - (r + δ + 1)), sq_nonneg δ]
  exact (isCompact_closedBall z (r + δ + 1)).of_isClosed_subset (isClosed_tsupport _) hsub

/-- The support of a narrow bump lies within `η` of the circle in radius. -/
theorem circleDensity_support_radius {r δ η : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hwidth : δ ≤ r * η) (z x : ℂ)
    (hx : x ∈ Function.support (circleDensity r δ hδ z)) :
    |‖x - z‖ - r| < η := by
  have h := circleDensity_support r δ hδ z x hx
  have hn : 0 ≤ ‖x - z‖ := norm_nonneg _
  rw [abs_lt] at h ⊢
  constructor
  · by_contra hc
    have hf : 0 ≤ (r - ‖x - z‖ - η) * (r + ‖x - z‖) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith [mul_nonneg (show 0 ≤ η by nlinarith) hn]
  · by_contra hc
    have hf : 0 ≤ (‖x - z‖ - r - η) * (r + ‖x - z‖) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith [mul_nonneg (show 0 ≤ η by nlinarith) hn]

/-- A sufficiently narrow squared-radius bump is supported in an enlarged disk. -/
theorem circleDensity_tsupport_subset_closedBall {r δ η : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hwidth : δ ≤ r * η) (z : ℂ) :
    tsupport (circleDensity r δ hδ z) ⊆ closedBall z (r + η) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have h := circleDensity_support r δ hδ z x hx
  have hn : 0 ≤ ‖x - z‖ := norm_nonneg _
  rw [abs_lt] at h
  rw [mem_closedBall, dist_eq_norm]
  nlinarith [sq_nonneg (‖x - z‖ - r)]

/-- A narrow density is a test function whenever the enlarged disk is local. -/
theorem circleDensity_isTestFunction {r δ η : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hwidth : δ ≤ r * η)
    (z : ℂ) (U : Set ℂ) (hU : closedBall z (r + η) ⊆ U) :
    IsTestFunction U (circleDensity r δ hδ z) :=
  ⟨circleDensity_contDiff r δ hδ z, circleDensity_hasCompactSupport hr.le hδ z,
    (circleDensity_tsupport_subset_closedBall hr hδ hwidth z).trans hU⟩

/-- The density is nonnegative and equals one at each point of its circle. -/
theorem circleDensity_nonneg (r δ : ℝ) (hδ : 0 < δ) (z x : ℂ) :
    0 ≤ circleDensity r δ hδ z x := (circleRadiusBump r δ hδ).nonneg

theorem circleDensity_eq_one {r : ℝ} {δ : ℝ} (hδ : 0 < δ)
    (z x : ℂ) (hx : dist x z = r) : circleDensity r δ hδ z x = 1 := by
  apply (circleRadiusBump r δ hδ).one_of_mem_closedBall
  simp [mem_closedBall, ← dist_eq_norm, hx, circleRadiusBump]
  positivity

/-- The mass of an annular density is strictly positive. -/
theorem circleDensity_integral_pos {r : ℝ} (hr : 0 ≤ r) {δ : ℝ} (hδ : 0 < δ)
    (z : ℂ) : 0 < ∫ x, circleDensity r δ hδ z x := by
  apply (circleDensity_contDiff r δ hδ z).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (circleDensity_hasCompactSupport hr hδ z) (circleDensity_nonneg r δ hδ z)
    (x := z + (r : ℂ))
  rw [circleDensity_eq_one hδ z _]
  · norm_num
  · simp [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hr]

/-- Translating the center does not change the mass. -/
theorem circleDensity_integral_eq (r δ : ℝ) (hδ : 0 < δ) (z : ℂ) :
    (∫ x, circleDensity r δ hδ z x) = ∫ x, circleDensity r δ hδ 0 x := by
  simpa [circleDensity] using
    (integral_sub_right_eq_self (fun x : ℂ => circleRadiusBump r δ hδ (‖x‖ ^ 2)) z)

/-- Dividing by the common positive mass gives a probability density. -/
theorem circleDensity_normalized_integral {r δ : ℝ} (hr : 0 ≤ r)
    (hδ : 0 < δ) (z : ℂ) :
    (∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x) = 1 := by
  rw [integral_const_mul, circleDensity_integral_eq r δ hδ z,
    inv_mul_cancel₀ (ne_of_gt (circleDensity_integral_pos hr hδ 0))]

/-- The difference of normalized annular densities is a local zero-integral
 test function. The two circles need a common local buffer. -/
theorem circleDensity_normalized_difference_test {r δ η : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hwidth : δ ≤ r * η) (z : ℂ) (U : Set ℂ)
    (hz : closedBall z (r + η) ⊆ U) (h0 : closedBall 0 (r + η) ⊆ U) :
    let m := ∫ x, circleDensity r δ hδ 0 x
    let φ := fun x => m⁻¹ * circleDensity r δ hδ z x - m⁻¹ * circleDensity r δ hδ 0 x
    IsTestFunction U φ ∧ ∫ x, φ x = 0 := by
  dsimp only
  let m := ∫ x, circleDensity r δ hδ 0 x
  have hztest := circleDensity_isTestFunction hr hδ hwidth z U hz
  have h0test := circleDensity_isTestFunction hr hδ hwidth 0 U h0
  constructor
  · simpa only [sub_eq_add_neg, neg_mul] using
      hztest.const_mul_add_const_mul h0test m⁻¹ (-m⁻¹)
  · have hzi : Integrable (circleDensity r δ hδ z) volume := (circleDensity_contDiff r δ hδ z).continuous.integrable_of_hasCompactSupport
      (circleDensity_hasCompactSupport hr.le hδ z)
    have h0i : Integrable (circleDensity r δ hδ 0) volume := (circleDensity_contDiff r δ hδ 0).continuous.integrable_of_hasCompactSupport
      (circleDensity_hasCompactSupport hr.le hδ 0)
    rw [integral_sub (hzi.const_mul _) (h0i.const_mul _), integral_const_mul,
      integral_const_mul, circleDensity_integral_eq r δ hδ z, sub_self]

end HarmonicBalls
