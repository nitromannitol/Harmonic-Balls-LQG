import HarmonicBalls.Proofs.Sec2.PolyHighProb

/-!
# Dyadic interpolation

Small positive scales lie between two successive dyadic scales, with the
index beyond any fixed threshold once the scale is sufficiently small.
-/

namespace HarmonicBalls

/-- A sufficiently small positive scale is bounded above by a dyadic scale
whose index is at least `N` and which is less than twice the scale. -/
theorem exists_late_dyadic_scale (N : ℕ) {x : ℝ} (hx : 0 < x)
    (hxN : x < ((2 : ℝ)⁻¹) ^ N) :
    ∃ n : ℕ, N ≤ n ∧ x ≤ ((2 : ℝ)⁻¹) ^ n ∧ ((2 : ℝ)⁻¹) ^ n < 2 * x := by
  have hx1 : x ≤ 1 := hxN.le.trans (pow_le_one₀ (by norm_num) (by norm_num))
  obtain ⟨n, hnlow, hnup⟩ := exists_nat_pow_near_of_lt_one hx hx1
    (show (0 : ℝ) < (2 : ℝ)⁻¹ by norm_num) (by norm_num)
  refine ⟨n, ?_, hnup, ?_⟩
  · by_contra h
    have hnN : n + 1 ≤ N := by omega
    have hp : ((2 : ℝ)⁻¹) ^ N ≤ ((2 : ℝ)⁻¹) ^ (n + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hnN
    linarith
  · rw [pow_succ] at hnlow
    linarith

end HarmonicBalls
