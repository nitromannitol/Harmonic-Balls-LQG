import HarmonicBalls.Proofs.Sec11.PinchBaseInternalAffine

/-! # Exponent margin for the square-diameter tail

The numerical exponent is the one appearing in Dubédat, Falconet, Gwynne,
Pfeffer and Sun, Lemma 3.19, equation (3.63). This file proves only the
parameter inequalities; it does not assert the weak LQG metric estimate. -/

namespace HarmonicBalls

/-- Subcritical Liouville charge gives the strict inequality `Q > 2`. -/
theorem two_lt_lqgQ_of_subcritical {γ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) :
    2 < lqgQ γ := by
  have hsq : 0 < (γ - 2) ^ 2 := sq_pos_of_ne_zero (by linarith)
  unfold lqgQ
  have hcalc : 0 < (γ - 2) ^ 2 / (2 * γ) := div_pos hsq (by positivity)
  field_simp at hcalc ⊢
  nlinarith

/-- A positive diameter exponent leaves a tail exponent strictly greater than
2, so a union bound over a two-dimensional dyadic grid can decay. -/
theorem exists_square_diameter_tail_exponent {ξ Q : ℝ}
    (hξ : 0 < ξ) (hQ : 2 < Q) :
    ∃ s p : ℝ, 0 < s ∧ s < ξ * Q ∧ 2 < p ∧
      p < (ξ * Q - s) ^ 2 / (2 * ξ ^ 2) := by
  let s := ξ * (Q - 2) / 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hsQ : s < ξ * Q := by dsimp [s]; nlinarith
  have hexp : 2 < (ξ * Q - s) ^ 2 / (2 * ξ ^ 2) := by
    have hξsq : 0 < ξ ^ 2 := sq_pos_of_pos hξ
    have hQsq : 0 < (Q - 2) * (Q + 6) := mul_pos (by linarith) (by linarith)
    apply (lt_div_iff₀ (by positivity : 0 < 2 * ξ ^ 2)).2
    dsimp [s]
    nlinarith [sq_nonneg (ξ * (Q - 2)), mul_pos hξsq hQsq]
  refine ⟨s, (2 + (ξ * Q - s) ^ 2 / (2 * ξ ^ 2)) / 2, hs, hsQ, ?_, ?_⟩ <;> linarith

/-- The exponent margin applies to every subcritical LQG parameter. -/
theorem exists_lqg_square_diameter_tail_exponent {γ ξ : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hξ : 0 < ξ) :
    ∃ s p : ℝ, 0 < s ∧ s < ξ * lqgQ γ ∧ 2 < p ∧
      p < (ξ * lqgQ γ - s) ^ 2 / (2 * ξ ^ 2) :=
  exists_square_diameter_tail_exponent hξ (two_lt_lqgQ_of_subcritical hγ hγ₂)

#print axioms two_lt_lqgQ_of_subcritical
#print axioms exists_square_diameter_tail_exponent
#print axioms exists_lqg_square_diameter_tail_exponent
end HarmonicBalls
