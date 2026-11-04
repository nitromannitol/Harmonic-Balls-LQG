import HarmonicBalls.Defs.GFF

/-!
# Affine covariance of whole-plane GFF increments

The additive normalization terms in the whole-plane Green kernel cancel in a
four-point increment.  Away from the diagonal, the resulting expression is
invariant under every nonconstant complex affine map.
-/

namespace HarmonicBalls

/-- The off-diagonal decomposition of the normalized whole-plane kernel. -/
theorem wholePlaneCov_eq_log_sub {z w : ℂ} (hzw : z ≠ w) :
    wholePlaneCov z w = Real.log (max ‖z‖ 1) + Real.log (max ‖w‖ 1) -
      Real.log ‖z - w‖ := by
  have hz : max ‖z‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  have hw : max ‖w‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  have hsub : ‖z - w‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzw)
  rw [wholePlaneCov, Real.log_div (mul_ne_zero hz hw) hsub, Real.log_mul hz hw]

/-- An affine change of coordinates changes the kernel by one-point terms and
the logarithm of the scale. The statement is off-diagonal because the kernel
uses a finite convention at coincident points. -/
theorem wholePlaneCov_affine {a b x y : ℂ} (ha : a ≠ 0) (hxy : x ≠ y) :
    wholePlaneCov (a * x + b) (a * y + b) = wholePlaneCov x y +
      (Real.log (max ‖a * x + b‖ 1) - Real.log (max ‖x‖ 1)) +
      (Real.log (max ‖a * y + b‖ 1) - Real.log (max ‖y‖ 1)) - Real.log ‖a‖ := by
  have hmap : a * x + b ≠ a * y + b := by
    intro h
    exact hxy (mul_left_cancel₀ ha (add_right_cancel h))
  have hdiff : (a * x + b) - (a * y + b) = a * (x - y) := by ring
  rw [wholePlaneCov_eq_log_sub hmap, wholePlaneCov_eq_log_sub hxy,
    hdiff, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr ha)
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))]
  ring

/-- Four-point increments of the normalized kernel depend only on distances. -/
theorem wholePlaneCov_four_point {x y u v : ℂ}
    (hxy : x ≠ y) (hxv : x ≠ v) (huy : u ≠ y) (huv : u ≠ v) :
    wholePlaneCov x y - wholePlaneCov x v - wholePlaneCov u y + wholePlaneCov u v =
      -Real.log ‖x - y‖ + Real.log ‖x - v‖ + Real.log ‖u - y‖ - Real.log ‖u - v‖ := by
  rw [wholePlaneCov_eq_log_sub hxy, wholePlaneCov_eq_log_sub hxv,
    wholePlaneCov_eq_log_sub huy, wholePlaneCov_eq_log_sub huv]
  ring

/-- Four-point covariance increments are invariant under complex affine maps
with nonzero linear coefficient, provided all four cross-pairs are distinct. -/
theorem wholePlaneCov_four_point_affine {a b x y u v : ℂ} (ha : a ≠ 0)
    (hxy : x ≠ y) (hxv : x ≠ v) (huy : u ≠ y) (huv : u ≠ v) :
    wholePlaneCov (a * x + b) (a * y + b) -
      wholePlaneCov (a * x + b) (a * v + b) -
      wholePlaneCov (a * u + b) (a * y + b) +
      wholePlaneCov (a * u + b) (a * v + b) =
    wholePlaneCov x y - wholePlaneCov x v - wholePlaneCov u y + wholePlaneCov u v := by
  have hinj {s t : ℂ} (hst : s ≠ t) : a * s + b ≠ a * t + b := by
    intro h
    exact hst (mul_left_cancel₀ ha (add_right_cancel h))
  have hlog {s t : ℂ} (hst : s ≠ t) :
      Real.log ‖(a * s + b) - (a * t + b)‖ = Real.log ‖a‖ + Real.log ‖s - t‖ := by
    have hdiff : (a * s + b) - (a * t + b) = a * (s - t) := by ring
    rw [hdiff, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr ha)
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hst))]
  rw [wholePlaneCov_four_point (hinj hxy) (hinj hxv) (hinj huy) (hinj huv),
    wholePlaneCov_four_point hxy hxv huy huv,
    hlog hxy, hlog hxv, hlog huy, hlog huv]
  ring

end HarmonicBalls
