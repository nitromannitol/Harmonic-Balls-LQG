import HarmonicBalls.Proofs.Sec11.CorrectedPinchThresholdTransfer

/-! Selection of the two positive Weyl heights from deterministic bounds. -/

namespace HarmonicBalls

open scoped ENNReal

/-- A positive Weyl parameter permits arbitrarily large exponential weights
with nonnegative height. -/
theorem exists_nonneg_weyl_height_above {ξ : ℝ} (hξ : 0 < ξ) (R : ℝ) :
    ∃ a : ℝ, 0 ≤ a ∧ R < Real.exp (ξ * a) := by
  let a : ℝ := (max R 0 + 1) / ξ
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have heq : ξ * a = max R 0 + 1 := by dsimp [a]; field_simp
  refine ⟨a, ha, ?_⟩
  rw [heq]
  have he := Real.add_one_le_exp (max R 0 + 1)
  have hr := le_max_left R 0
  linarith

/-- The obstacle and root bump heights can be chosen uniformly from four
natural-number bounds whenever the Weyl parameter is positive. -/
theorem exists_first_pinch_weyl_heights {ξ : ℝ} (hξ : 0 < ξ)
    (n m k l : ℕ) (hn : 0 < n) (hk : 0 < k) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      ENNReal.ofReal (Real.exp (ξ * b)) * m <
        ENNReal.ofReal (Real.exp (ξ * a)) * (n : ℝ≥0∞)⁻¹ ∧
      (l : ℝ≥0∞) < ENNReal.ofReal (Real.exp (ξ * b)) * (k : ℝ≥0∞)⁻¹ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨b, hb, hbexp⟩ := exists_nonneg_weyl_height_above hξ ((l : ℝ) * k)
  obtain ⟨a, ha, haexp⟩ := exists_nonneg_weyl_height_above hξ
    (Real.exp (ξ * b) * m * n)
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · have hh : Real.exp (ξ * b) * m < Real.exp (ξ * a) * (n : ℝ)⁻¹ := by
      apply (lt_mul_inv_iff₀ hn').2
      exact haexp
    have hh' := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity : 0 ≤ Real.exp (ξ * b) * m)).2 hh
    rw [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_mul (Real.exp_nonneg _),
      ENNReal.ofReal_inv_of_pos hn', ENNReal.ofReal_natCast, ENNReal.ofReal_natCast] at hh'
    exact hh'
  · have hh : (l : ℝ) < Real.exp (ξ * b) * (k : ℝ)⁻¹ := by
      apply (lt_mul_inv_iff₀ hk').2
      exact hbexp
    have hh' := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity : 0 ≤ (l : ℝ))).2 hh
    rw [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_inv_of_pos hk',
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast] at hh'
    exact hh'

#print axioms exists_nonneg_weyl_height_above
#print axioms exists_first_pinch_weyl_heights

end HarmonicBalls
