import HarmonicBalls.Proofs.Sec11.PinchTailExponent

/-! # Summability of square-diameter tail bounds

This numerical calculation does not assert the weak LQG metric estimate. -/

namespace HarmonicBalls

/-- A tail exponent greater than two compensates for the `4^n` dyadic
squares at level `n` and yields a summable sequence. -/
theorem summable_dyadic_square_count_mul_tail {p : ℝ} (hp : 2 < p) :
    Summable (fun n : ℕ => (4 : ℝ) ^ n * (1 / 2 : ℝ) ^ (p * n)) := by
  have h0 : 0 ≤ (1 / 2 : ℝ) ^ (p - 2) := Real.rpow_nonneg (by norm_num) _
  have h1 : (1 / 2 : ℝ) ^ (p - 2) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hsum := summable_geometric_of_lt_one h0 h1
  convert hsum using 1
  funext n
  have hpow : ((1 / 2 : ℝ) ^ (p - 2)) ^ n =
      (1 / 2 : ℝ) ^ ((p - 2) * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [hpow]
  have he : p * (n : ℝ) = 2 * n + (p - 2) * n := by ring
  rw [he, Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
  have htwo : (1 / 2 : ℝ) ^ (2 * (n : ℝ)) = (1 / 4 : ℝ) ^ n := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.rpow_natCast]
    norm_num
  rw [htwo]
  rw [← mul_assoc, ← mul_pow]
  norm_num

/-- At subcritical charge one can choose a positive square-diameter exponent
whose corresponding grid-level tail bounds are summable. -/
theorem exists_summable_lqg_square_tail {γ ξ : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hξ : 0 < ξ) :
    ∃ s p : ℝ, 0 < s ∧ s < ξ * lqgQ γ ∧ 2 < p ∧
      p < (ξ * lqgQ γ - s) ^ 2 / (2 * ξ ^ 2) ∧
      Summable (fun n : ℕ => (4 : ℝ) ^ n * (1 / 2 : ℝ) ^ (p * n)) := by
  obtain ⟨s, p, hs, hsQ, hp, hpQ⟩ :=
    exists_lqg_square_diameter_tail_exponent hγ hγ₂ hξ
  exact ⟨s, p, hs, hsQ, hp, hpQ, summable_dyadic_square_count_mul_tail hp⟩

/-- The subcritical parameter range permits the small-square diameter
exponent from the weak-metric estimate and a summable dyadic union bound. -/
theorem exists_summable_lqg_square_tail_below_holder_exponent {γ ξ : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hξ : 0 < ξ) :
    ∃ s p : ℝ, 0 < s ∧ s < ξ * (lqgQ γ - 2) ∧
      s < ξ * lqgQ γ ∧ 2 < p ∧
      p < (ξ * lqgQ γ - s) ^ 2 / (2 * ξ ^ 2) ∧
      Summable (fun n : ℕ => (4 : ℝ) ^ n * (1 / 2 : ℝ) ^ (p * n)) := by
  have hQ := two_lt_lqgQ_of_subcritical hγ hγ₂
  let s := ξ * (lqgQ γ - 2) / 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hsh : s < ξ * (lqgQ γ - 2) := by dsimp [s]; nlinarith
  have hsQ : s < ξ * lqgQ γ := by dsimp [s]; nlinarith
  have hq : 2 < (ξ * lqgQ γ - s) ^ 2 / (2 * ξ ^ 2) :=
    metricDiameterTailExponent_gt_two hξ hsh
  let p := (2 + (ξ * lqgQ γ - s) ^ 2 / (2 * ξ ^ 2)) / 2
  have hp : 2 < p := by dsimp [p]; linarith
  have hpq : p < (ξ * lqgQ γ - s) ^ 2 / (2 * ξ ^ 2) := by
    dsimp [p]; linarith
  exact ⟨s, p, hs, hsh, hsQ, hp, hpq, summable_dyadic_square_count_mul_tail hp⟩

end HarmonicBalls
