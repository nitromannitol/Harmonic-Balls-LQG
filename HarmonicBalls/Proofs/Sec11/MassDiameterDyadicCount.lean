import HarmonicBalls.Proofs.Sec11.MassDiameterCommonFactor

/-! # Dyadic square counts for mass and diameter estimates -/

namespace HarmonicBalls
open MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators

/-- A square grid with `2 ^ n` intervals in each coordinate has `4 ^ n` tiles. -/
theorem dyadic_square_grid_card (n : ℕ) :
    (Fintype.card (Fin (2 ^ n) × Fin (2 ^ n)) : ℝ≥0∞) = (4 : ℝ≥0∞) ^ n := by
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
  rw [← mul_pow]
  norm_num

/-- A uniform geometric failure bound on each square of a dyadic grid is
summable over the grid as soon as its rate is strictly less than one quarter. -/
theorem tendsto_dyadic_square_failure_sum
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ∀ n, Fin (2 ^ n) × Fin (2 ^ n) → Set Ω)
    (C q : ℝ≥0∞) (hC : C ≠ ∞) (hq : 4 * q < 1)
    (hbound : ∀ n i, P (B n i) ≤ C * q ^ n) :
    Tendsto (fun n => ∑ i : Fin (2 ^ n) × Fin (2 ^ n), P (B n i)) atTop (𝓝 0) := by
  apply tendsto_sum_tile_failures_of_geometric_bound P
    (fun n => Fin (2 ^ n) × Fin (2 ^ n)) B 1 C 4 q (by simp) hC hq
  · intro n
    simpa only [one_mul] using le_of_eq (dyadic_square_grid_card n)
  · exact hbound

/-- The pinned circle-average normalization and a geometric per-square
estimate imply that all dyadic square diameters are small with high probability. -/
theorem IsWholePlaneGFF.tendsto_dyadic_square_diameters
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (ξ : ℝ)
    (X : ∀ n, Fin (2 ^ n) × Fin (2 ^ n) → Ω → ℝ≥0∞)
    (a : ℕ → ℝ≥0∞) (d C q : ℝ≥0∞)
    (hCfinite : C ≠ ∞) (hq : 4 * q < 1) (hmargin : ∀ n, a n < d)
    (hbound : ∀ n i, P {ω | a n * ENNReal.ofReal
      (Real.exp (ξ * hcirc ω 1 0)) < X n i ω} ≤ C * q ^ n) :
    Tendsto (fun n => P {ω | ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      X n i ω < d}ᶜ) atTop (𝓝 0) := by
  apply h.tendsto_all_tiles_failure_of_pinned_circle_factor ξ
    (fun n => Fin (2 ^ n) × Fin (2 ^ n)) X a d hmargin
  exact tendsto_dyadic_square_failure_sum P _ C q hCfinite hq hbound

end HarmonicBalls
