import HarmonicBalls.Steps.Sec11.ScaleRatioFinitePrefix

/-! # Exponential scale bounds and exponent margins

Deterministic consequences of a power bound on metric scaling constants and
of the subcritical LQG parameter range. -/

namespace HarmonicBalls

open Filter
open scoped ENNReal

/-- A stronger eventual exponential decay gives a uniform bound for the
normalization at every natural scale. -/
theorem exists_uniform_scale_ratio_of_eventually_power_bound
    (a : ℕ → ℝ≥0∞) (s η θ : ℝ) (hgap : η < θ)
    (ha : ∀ n, a n ≠ ∞) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (h : ∀ᶠ n in atTop,
      a n ≤ C * ENNReal.ofReal (Real.exp (-θ * (s + (n : ℝ))))) :
    ∃ A : ℝ≥0∞, A ≠ ∞ ∧ ∀ n,
      a n / ENNReal.ofReal (Real.exp (-η * (n : ℝ))) ≤ A := by
  apply exists_uniform_exponential_scale_ratio_of_eventually_le a η ha
    (C * ENNReal.ofReal (Real.exp (-θ * s)))
    (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top)
  filter_upwards [h] with n hn
  have hr : ENNReal.ofReal (Real.exp (-θ * (s + (n : ℝ)))) /
      ENNReal.ofReal (Real.exp (-η * (n : ℝ))) ≤
        ENNReal.ofReal (Real.exp (-θ * s)) := by
    rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _),
      ← Real.exp_neg, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt hgap)) hn0]
  calc
    _ ≤ (C * ENNReal.ofReal (Real.exp (-θ * (s + (n : ℝ))))) /
        ENNReal.ofReal (Real.exp (-η * (n : ℝ))) := by gcongr
    _ = C * (ENNReal.ofReal (Real.exp (-θ * (s + (n : ℝ)))) /
        ENNReal.ofReal (Real.exp (-η * (n : ℝ)))) := by rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
    _ ≤ _ := by gcongr

/-- The subcritical LQG parameter satisfies `γ < Q`. -/
theorem gamma_lt_lqgQ {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : γ < lqgQ γ := by
  have hsq : γ ^ 2 < 4 := by nlinarith
  have hdiv : γ / 2 < 2 / γ := by
    apply (lt_div_iff₀ hγ).2
    nlinarith
  unfold lqgQ
  linarith

/-- There is room for four intermediate exponents even at `α = γ`. -/
theorem exists_subcritical_exponent_margins {γ ξ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hξ : 0 < ξ) (hα : α ≤ γ) :
    ∃ β κ η θ : ℝ, ξ * α < β ∧ β < κ ∧ κ < η ∧ η < θ ∧
      θ < ξ * lqgQ γ := by
  have hgap : ξ * α < ξ * lqgQ γ :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hα hξ.le)
      (mul_lt_mul_of_pos_left (gamma_lt_lqgQ hγ hγ2) hξ)
  obtain ⟨κ, hκ₁, hκ₂⟩ := exists_between hgap
  obtain ⟨β, hβ₁, hβ₂⟩ := exists_between hκ₁
  obtain ⟨η, hη₁, hη₂⟩ := exists_between hκ₂
  obtain ⟨θ, hθ₁, hθ₂⟩ := exists_between hη₂
  exact ⟨β, κ, η, θ, hβ₁, hβ₂, hη₁, hθ₁, hθ₂⟩

/-- First moments are admissible in the diameter moment range whenever the
metric dimension is at least one and `0 < γ < 2`. -/
theorem one_lt_four_mul_dimension_div_gamma_sq {γ d : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hd : 1 ≤ d) :
    (1 : ℝ) < 4 * d / γ ^ 2 := by
  apply (lt_div_iff₀ (sq_pos_of_pos hγ)).2
  nlinarith

#print axioms exists_uniform_scale_ratio_of_eventually_power_bound
#print axioms gamma_lt_lqgQ
#print axioms exists_subcritical_exponent_margins
#print axioms one_lt_four_mul_dimension_div_gamma_sq

end HarmonicBalls
