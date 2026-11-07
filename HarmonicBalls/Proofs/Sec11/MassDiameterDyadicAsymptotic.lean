import HarmonicBalls.Proofs.Sec11.MassDiameterDyadicCount

/-! # Asymptotic dyadic square estimates -/

namespace HarmonicBalls
open MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators

/-- Exponents above two beat the growth of a planar dyadic square grid. -/
theorem dyadic_decay_rate_lt_quarter (p : ℝ) (hp : 2 < p) :
    4 * ENNReal.ofReal ((1 / 2 : ℝ) ^ p) < 1 := by
  have h : (1 / 2 : ℝ) ^ p < 1 / 4 := by
    have h' := Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hp
    norm_num [Real.rpow_two] at h' ⊢
    exact h'
  have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) _
  have hreal : (4 : ℝ) * (1 / 2 : ℝ) ^ p < 1 := by linarith
  have := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).2 hreal
  simpa [ENNReal.ofReal_mul, hnonneg] using this

/-- Only sufficiently fine scales need satisfy the per-square geometric
estimate; the finitely many coarser scales do not affect the limit. -/
theorem tendsto_dyadic_square_failure_sum_of_eventually
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ∀ n, Fin (2 ^ n) × Fin (2 ^ n) → Set Ω)
    (C q : ℝ≥0∞) (hC : C ≠ ∞) (hq : 4 * q < 1)
    (hbound : ∀ᶠ n in atTop, ∀ i, P (B n i) ≤ C * q ^ n) :
    Tendsto (fun n => ∑ i : Fin (2 ^ n) × Fin (2 ^ n), P (B n i)) atTop (𝓝 0) := by
  classical
  let B' : ∀ n, Fin (2 ^ n) × Fin (2 ^ n) → Set Ω :=
    fun n i => if ∀ i, P (B n i) ≤ C * q ^ n then B n i else ∅
  have hb : ∀ n i, P (B' n i) ≤ C * q ^ n := by
    intro n i
    by_cases hn : ∀ i, P (B n i) ≤ C * q ^ n
    · change P (if ∀ i, P (B n i) ≤ C * q ^ n then B n i else ∅) ≤ _
      rw [ite_eq_left hn]
      exact hn i
    · change P (if ∀ i, P (B n i) ≤ C * q ^ n then B n i else ∅) ≤ _
      rw [ite_eq_right hn, measure_empty]
      exact zero_le
  have hlim := tendsto_dyadic_square_failure_sum P B' C q hC hq hb
  apply hlim.congr'
  filter_upwards [hbound] with n hn
  simp [B', hn]

/-- A sufficiently fine-scale geometric estimate gives simultaneous control
of all dyadic square observables for a pinned whole-plane GFF. -/
theorem IsWholePlaneGFF.tendsto_dyadic_square_diameters_of_eventually
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (ξ : ℝ)
    (X : ∀ n, Fin (2 ^ n) × Fin (2 ^ n) → Ω → ℝ≥0∞)
    (a : ℕ → ℝ≥0∞) (d C q : ℝ≥0∞)
    (hCfinite : C ≠ ∞) (hq : 4 * q < 1) (hmargin : ∀ n, a n < d)
    (hbound : ∀ᶠ n in atTop, ∀ i, P {ω | a n * ENNReal.ofReal
      (Real.exp (ξ * hcirc ω 1 0)) < X n i ω} ≤ C * q ^ n) :
    Tendsto (fun n => P {ω | ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      X n i ω < d}ᶜ) atTop (𝓝 0) := by
  apply h.tendsto_all_tiles_failure_of_pinned_circle_factor ξ
    (fun n => Fin (2 ^ n) × Fin (2 ^ n)) X a d hmargin
  exact tendsto_dyadic_square_failure_sum_of_eventually P _ C q hCfinite hq hbound

#print axioms IsWholePlaneGFF.tendsto_dyadic_square_diameters_of_eventually
#print axioms dyadic_decay_rate_lt_quarter
#print axioms tendsto_dyadic_square_failure_sum_of_eventually
end HarmonicBalls
