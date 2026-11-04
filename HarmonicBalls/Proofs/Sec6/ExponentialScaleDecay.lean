import HarmonicBalls.Proofs.Sec6.GeometricScaleWindow

/-! # Exponential decay in a logarithmic scale window -/

namespace HarmonicBalls.Section6

open MeasureTheory
open scoped ENNReal

/-- Exponential decay in the number of scales is a power of the lower
radius when the number of scales grows at least logarithmically. -/
theorem exp_neg_mul_le_rpow_of_logb {b ε α D K : ℝ}
    (hb : 1 < b) (hε : 0 < ε) (hα : 0 ≤ α) (hD : 0 < D)
    (hK : Real.logb b (ε ^ (-1 : ℝ)) / D ≤ K) :
    Real.exp (-α * K) ≤ ε ^ (α / (D * Real.log b)) := by
  have hlogb : Real.logb b (ε ^ (-1 : ℝ)) = -Real.log ε / Real.log b := by
    rw [Real.rpow_neg_one, Real.logb, Real.log_inv]
  have hlogpos : 0 < Real.log b := Real.log_pos hb
  rw [hlogb] at hK
  have hcomp := mul_le_mul_of_nonpos_left hK (neg_nonpos.mpr hα)
  have hid : (-Real.log ε / Real.log b / D) * (-α) =
      Real.log ε * (α / (D * Real.log b)) := by
    field_simp
  have hcomp' : -α * K ≤ Real.log ε * (α / (D * Real.log b)) := by
    calc
      _ ≤ -α * (-Real.log ε / Real.log b / D) := hcomp
      _ = _ := by rw [mul_comm]; exact hid
  rw [Real.rpow_def_of_pos hε]
  exact Real.exp_le_exp.mpr hcomp'

/-- The same estimate with the positive prefactor and extended-real measure
bound used in the annulus iteration lemma. -/
theorem ofReal_exp_bound_le_rpow {b ε α D K C : ℝ}
    (hb : 1 < b) (hε : 0 < ε) (hα : 0 ≤ α) (hD : 0 < D) (hC : 0 ≤ C)
    (hK : Real.logb b (ε ^ (-1 : ℝ)) / D ≤ K) :
    ENNReal.ofReal (C * Real.exp (-α * K)) ≤
      ENNReal.ofReal (C * ε ^ (α / (D * Real.log b))) :=
  ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (exp_neg_mul_le_rpow_of_logb hb hε hα hD hK) hC)

end HarmonicBalls.Section6
