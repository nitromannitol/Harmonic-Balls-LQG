import HarmonicBalls.Steps.Sec11.CompactDiameterSpecialization

/-! # Finite prefixes of scale ratios

An eventual finite bound on positive-scale ratios extends to all natural
scales by absorbing the finite prefix into the constant.
-/

namespace HarmonicBalls

open MeasureTheory Filter
open scoped ENNReal

/-- An eventually bounded sequence of finite extended nonnegative reals has
a finite uniform bound. -/
theorem exists_finite_uniform_bound_of_eventually_le
    (f : ℕ → ℝ≥0∞) (hfin : ∀ n, f n ≠ ∞) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (h : ∀ᶠ n in atTop, f n ≤ C) :
    ∃ A : ℝ≥0∞, A ≠ ∞ ∧ ∀ n, f n ≤ A := by
  classical
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
  refine ⟨C + ∑ i ∈ Finset.range N, f i, ENNReal.add_ne_top.mpr ⟨hC, ?_⟩, ?_⟩
  · exact ENNReal.sum_ne_top.mpr (fun i _ => hfin i)
  · intro n
    by_cases hn : n < N
    · calc
        f n ≤ ∑ i ∈ Finset.range N, f i := by
          apply Finset.single_le_sum
          · intro i _
            exact bot_le
          · exact Finset.mem_range.mpr hn
        _ ≤ C + ∑ i ∈ Finset.range N, f i := le_add_left le_rfl
    · exact (hN n (Nat.le_of_not_gt hn)).trans (le_add_right le_rfl)

/-- An eventual bound for the ratio to an exponential scale extends to all
natural scales when the original deterministic scale constants are finite. -/
theorem exists_uniform_exponential_scale_ratio_of_eventually_le
    (a : ℕ → ℝ≥0∞) (η : ℝ) (ha : ∀ n, a n ≠ ∞)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (h : ∀ᶠ n in atTop,
      a n / ENNReal.ofReal (Real.exp (-η * (n : ℝ))) ≤ C) :
    ∃ A : ℝ≥0∞, A ≠ ∞ ∧ ∀ n,
      a n / ENNReal.ofReal (Real.exp (-η * (n : ℝ))) ≤ A := by
  apply exists_finite_uniform_bound_of_eventually_le _ _ C hC h
  intro n
  exact ENNReal.div_ne_top (ha n) (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

#print axioms exists_finite_uniform_bound_of_eventually_le
#print axioms exists_uniform_exponential_scale_ratio_of_eventually_le

end HarmonicBalls
