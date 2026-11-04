import HarmonicBalls.Proofs.Sec7.DyadicInterpolation

/-!
# Converting a dyadic spatial scale into a time increment

The time threshold `α s^(2β)` gives a shell radius of order
`T^(1/(4β))` when `s` is a dyadic scale comparable to `(T/α)^(1/(2β))`.
-/

namespace HarmonicBalls

/-- The mass threshold at a small scale is below the lower bound obtained
from a ball of one eighth that scale. -/
theorem rpow_double_le_div_eight_rpow {s β : ℝ} (hs : 0 < s) (hs8 : s ≤ 1 / 8)
    (hβ : 0 ≤ β) : s ^ (2 * β) ≤ (s / 8) ^ β := by
  have hs' : s ^ 2 ≤ s / 8 := by nlinarith
  calc
    s ^ (2 * β) = (s ^ 2) ^ β := by rw [← Real.rpow_two, ← Real.rpow_mul hs.le]
    _ ≤ (s / 8) ^ β := Real.rpow_le_rpow (sq_nonneg _) hs' hβ

/-- The selected scale has enough annulus mass for a time increment `T`. -/
theorem time_le_mul_rpow_of_scale {T α β s : ℝ} (hT : 0 < T) (hα : 0 < α) (hβ : 0 < β)
    (hs : (T / α) ^ (2 * β)⁻¹ ≤ s) : T ≤ α * s ^ (2 * β) := by
  have hx : 0 < T / α := div_pos hT hα
  have hspos : 0 < s := (Real.rpow_pos_of_pos hx _).trans_le hs
  have hpow : ((T / α) ^ (2 * β)⁻¹) ^ (2 * β) = T / α := by
    rw [← Real.rpow_mul hx.le, inv_mul_cancel₀ (by positivity : 2 * β ≠ 0), Real.rpow_one]
  have hle := Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) hs (by positivity : 0 ≤ 2 * β)
  rw [hpow] at hle
  have := mul_le_mul_of_nonneg_left hle hα.le
  have : α * (T / α) = T := by field_simp
  linarith

/-- A scale at most twice `(T/α)^(1/(2β))` yields the Hölder radius. -/
theorem sqrt_scale_le_time_rpow {T α β s : ℝ} (hT : 0 < T) (hα : 0 < α) (hβ : 0 < β)
    (hs : 0 ≤ s) (hsupper : s ≤ 2 * (T / α) ^ (2 * β)⁻¹) :
    70 * Real.sqrt s ≤ 140 * α ^ (-(4 * β)⁻¹) * T ^ (4 * β)⁻¹ := by
  let x : ℝ := (T / α) ^ (2 * β)⁻¹
  have hx : 0 < x := Real.rpow_pos_of_pos (div_pos hT hα) _
  have hsqrt : Real.sqrt s ≤ 2 * Real.sqrt x := by
    have hsq1 := Real.sq_sqrt hs
    have hsq2 := Real.sq_sqrt hx.le
    have h1 := Real.sqrt_nonneg s
    have h2 := Real.sqrt_nonneg x
    dsimp [x] at hx
    nlinarith
  have hroot : Real.sqrt x = α ^ (-(4 * β)⁻¹) * T ^ (4 * β)⁻¹ := by
    dsimp [x]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (div_pos hT hα).le]
    have hexp : (2 * β)⁻¹ * (1 / 2 : ℝ) = (4 * β)⁻¹ := by field_simp; ring
    rw [hexp, Real.div_rpow hT.le hα.le, div_eq_mul_inv, ← Real.rpow_neg hα.le, mul_comm]
  rw [mul_assoc, ← hroot]
  linarith

end HarmonicBalls
