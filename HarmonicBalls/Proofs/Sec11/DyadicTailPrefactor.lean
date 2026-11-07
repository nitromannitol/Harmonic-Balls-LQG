import HarmonicBalls.Proofs.Sec11.DyadicClosedSquareTail

/-! # Fixed prefactors in dyadic power bounds

These deterministic estimates do not assert an LQG metric moment bound. -/

namespace HarmonicBalls
open Filter Topology
open scoped ENNReal

/-- A fixed nonnegative prefactor and a fixed side-length scaling can be
absorbed into any smaller positive exponent, despite a vanishing error. -/
theorem dyadic_scaled_power_error_prefactor_eventually_le
    (A C p p' : ℝ) (hA : 0 ≤ A) (hC : 0 < C) (hp' : 0 < p') (hpp : p' < p)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      A * (C * (1 / 2 : ℝ) ^ n) ^ (p + e n) ≤
        (1 / 2 : ℝ) ^ (p' * n) := by
  let q := (p + p') / 2
  have hpq : p' < q := by dsimp [q]; linarith
  have hqp : q < p := by dsimp [q]; linarith
  have hq : 0 < q := hp'.trans hpq
  have hscale := dyadic_scaled_power_error_eventually_le C p q hC hq hqp e he
  have hfactor : ∀ᶠ n : ℕ in atTop,
      A * (1 / 2 : ℝ) ^ ((q - p') * n) < 1 := by
    filter_upwards [dyadic_diameter_threshold_eventually_lt A (q - p')
      (by linarith) 1 (by norm_num)] with n hn
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).1 hn
  filter_upwards [hscale, hfactor] with n hn hf
  calc
    A * (C * (1 / 2 : ℝ) ^ n) ^ (p + e n) ≤
        A * (1 / 2 : ℝ) ^ (q * n) := mul_le_mul_of_nonneg_left hn hA
    _ = (A * (1 / 2 : ℝ) ^ ((q - p') * n)) *
        (1 / 2 : ℝ) ^ (p' * n) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
      congr 2
      ring
    _ ≤ (1 / 2 : ℝ) ^ (p' * n) := by
      calc
        _ ≤ 1 * (1 / 2 : ℝ) ^ (p' * n) :=
          mul_le_mul_of_nonneg_right hf.le (Real.rpow_nonneg (by norm_num) _)
        _ = _ := one_mul _

#print axioms dyadic_scaled_power_error_prefactor_eventually_le
/-- A uniform intermediate-square tail with a fixed prefactor yields the
prefactor-free dyadic tail required by the pinch construction. -/
theorem dyadicIntermediateInternalDiameter_tail_of_prefactor
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (D : Ω → ℂ → ℂ → ℝ) (z : ℂ) (L : ℝ) (hL : 0 < L)
    (threshold : ℕ → Ω → ℝ≥0∞) (A p p' : ℝ)
    (hA : 0 ≤ A) (hp' : 0 < p') (hpp : p' < p)
    (e : ℝ → ℝ) (he : Tendsto e (𝓝[>] 0) (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      P {ω | threshold n ω < dyadicIntermediateInternalDiameter D z L n i ω} ≤
        ENNReal.ofReal (A * (3 * L / (2 * (2 : ℝ) ^ n)) ^
          (p + e (3 * L / (2 * (2 : ℝ) ^ n))))) :
    ∀ᶠ n in atTop, ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      P {ω | threshold n ω < dyadicIntermediateInternalDiameter D z L n i ω} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (p' * n)) := by
  have hscale := dyadic_scaled_power_error_prefactor_eventually_le A (3 * L / 2) p p'
    hA (by positivity) hp' hpp (fun n => e (3 * L / (2 * (2 : ℝ) ^ n)))
    (tendsto_intermediate_square_error L hL e he)
  filter_upwards [hbound, hscale] with n hn hs
  intro i
  have hside : 3 * L / (2 * (2 : ℝ) ^ n) = (3 * L / 2) * (1 / 2 : ℝ) ^ n := by
    rw [div_pow]
    field_simp
    ring
  exact (hn i).trans (ENNReal.ofReal_le_ofReal (by simpa only [hside] using hs))

#print axioms dyadicIntermediateInternalDiameter_tail_of_prefactor
end HarmonicBalls
