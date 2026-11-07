import HarmonicBalls.Proofs.Sec11.MassDiameterWeylGluing

/-! # Choice of a core contraction budget -/

namespace HarmonicBalls
open scoped ENNReal

/-- If the two tile entrance costs leave a positive margin, a sufficiently
negative Weyl exponent contracts any finite core cost into that margin. -/
theorem exists_negative_weyl_core_budget {a b ε : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hmargin : a + a < ε) :
    ∃ B : ℝ, B < 0 ∧
      ENNReal.ofReal a + ENNReal.ofReal (Real.exp B) * ENNReal.ofReal b +
        ENNReal.ofReal a < ENNReal.ofReal ε := by
  let q := (ε - (a + a)) / (b + 1)
  have hq : 0 < q := div_pos (by linarith) (by linarith)
  let B := min (-1 : ℝ) (Real.log q - 1)
  have hB : B < 0 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hexp : Real.exp B < q := by
    rw [← Real.exp_log hq]
    exact Real.exp_lt_exp.mpr (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have hreal : a + Real.exp B * b + a < ε := by
    have hqeq : q * (b + 1) = ε - (a + a) := by
      dsimp [q]
      field_simp
    have hmul : Real.exp B * (b + 1) < q * (b + 1) :=
      mul_lt_mul_of_pos_right hexp (by linarith)
    have he : 0 < Real.exp B := Real.exp_pos _
    nlinarith
  refine ⟨B, hB, ?_⟩
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← ENNReal.ofReal_add ha,
    ← ENNReal.ofReal_add (by positivity : 0 ≤ a + Real.exp B * b)]
  · exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 hreal
  all_goals positivity

#print axioms exists_negative_weyl_core_budget
end HarmonicBalls
