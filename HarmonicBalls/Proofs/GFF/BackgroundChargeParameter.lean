import HarmonicBalls.Defs.Notation

/-! # Background charge parameter

The deterministic parameter algebra for the background charge `Q` in
Bou-Rabee and Gwynne, equation (Q), and the Weyl exponent in equation (xi).
No identification of a metric or field is assumed or proved here. The broader
formalization uses the GFF construction of Leonardo Bonanno.
-/

namespace HarmonicBalls

/-- The difference of two background charges factors into positive terms when
`0 < a < b < 2`. -/
theorem lqgQ_sub_lqgQ {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    lqgQ a - lqgQ b = (b - a) * (4 - a * b) / (2 * a * b) := by
  unfold lqgQ
  field_simp
  ring

/-- The background charge is strictly decreasing on the subcritical range. -/
theorem lqgQ_strictAntiOn : StrictAntiOn lqgQ (Set.Ioo 0 2) := by
  intro a ha b hb hab
  have hab4 : a * b < 4 := by
    have h := mul_lt_mul_of_pos_right ha.2 hb.1
    have hb4 : 2 * b < 4 := by linarith [hb.2]
    exact lt_trans h hb4
  have hpos : 0 < (b - a) * (4 - a * b) / (2 * a * b) := by
    exact div_pos (mul_pos (sub_pos.mpr hab) (sub_pos.mpr hab4))
      (mul_pos (mul_pos (by norm_num) ha.1) hb.1)
  rw [← lqgQ_sub_lqgQ (ne_of_gt ha.1) (ne_of_gt hb.1)] at hpos
  linarith

/-- A subcritical parameter is determined by its background charge. -/
theorem lqgQ_injOn : Set.InjOn lqgQ (Set.Ioo 0 2) :=
  lqgQ_strictAntiOn.injOn

/-- Equality of charges identifies two subcritical LQG parameters. -/
theorem gamma_eq_of_lqgQ_eq {γ γ₀ : ℝ} (hγ : γ ∈ Set.Ioo 0 2)
    (hγ₀ : γ₀ ∈ Set.Ioo 0 2) (hQ : lqgQ γ = lqgQ γ₀) : γ = γ₀ :=
  lqgQ_injOn hγ hγ₀ hQ

/-- A positive LQG parameter has positive background charge. -/
theorem lqgQ_pos {γ : ℝ} (hγ : 0 < γ) : 0 < lqgQ γ := by
  unfold lqgQ
  positivity

/-- Once the background charges agree, equality of the scaling products
identifies the Weyl exponents. -/
theorem xi_eq_of_lqgQ_eq_of_mul_lqgQ_eq {γ γ₀ ξ ξ₀ : ℝ}
    (hγ : 0 < γ) (hQ : lqgQ γ = lqgQ γ₀)
    (hξQ : ξ * lqgQ γ = ξ₀ * lqgQ γ₀) : ξ = ξ₀ := by
  rw [← hQ] at hξQ
  exact mul_right_cancel₀ (ne_of_gt (lqgQ_pos hγ)) hξQ

/-- Conditional recovery of the physical parameter and normalization
`ξ = γ₀ / d`, from equality of the background charges and scaling products. -/
theorem gamma_eq_and_xi_eq_div_of_lqgQ_eq_of_mul_lqgQ_eq
    {γ γ₀ ξ d : ℝ} (hγ : γ ∈ Set.Ioo 0 2) (hγ₀ : γ₀ ∈ Set.Ioo 0 2)
    (hQ : lqgQ γ = lqgQ γ₀)
    (hξQ : ξ * lqgQ γ = (γ₀ / d) * lqgQ γ₀) :
    γ = γ₀ ∧ ξ = γ₀ / d :=
  ⟨gamma_eq_of_lqgQ_eq hγ hγ₀ hQ,
    xi_eq_of_lqgQ_eq_of_mul_lqgQ_eq hγ.1 hQ hξQ⟩

#print axioms lqgQ_sub_lqgQ
#print axioms lqgQ_strictAntiOn
#print axioms lqgQ_injOn
#print axioms gamma_eq_of_lqgQ_eq
#print axioms lqgQ_pos
#print axioms xi_eq_of_lqgQ_eq_of_mul_lqgQ_eq
#print axioms gamma_eq_and_xi_eq_div_of_lqgQ_eq_of_mul_lqgQ_eq

end HarmonicBalls
