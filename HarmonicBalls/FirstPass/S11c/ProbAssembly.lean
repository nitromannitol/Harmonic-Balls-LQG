import HarmonicBalls.FirstPass.S11c.DyadicGrid

/-!
# Proposition 11.10, helpers for the final assembly (fp-S11c, owner n1)

FIRST-PASS NEW (bookkeeping). The assembly of the printed proof of `lemma:mass-diam` (paper lines 3091-3112) uses four small
facts: (i) an event of probability at least `1 - δ` has complement of measure at most `δ` (the inner small-cell event of
`DyadicCellDiamSmallFrozen` and the exterior event of `exists_measurable_exterior_bound`); (ii) an inclusion of integer grid
boxes is monotone in the endpoints; (iii) a closed dyadic square of level `N` is the grid box of mesh `2^{-(N+3)}` with the
cell `[j 8, j 8 + 8]` (`d = 3`); (iv) a closed dyadic square is a closed rectangle.
-/

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicBalls

/-- An event of probability at least `1 - δ` has complement of measure at most `δ`. -/
lemma prob_compl_le_ofReal_of_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {A : Set Ω} (hA : MeasurableSet A) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (h : ENNReal.ofReal (1 - δ) ≤ P A) : P Aᶜ ≤ ENNReal.ofReal δ := by
  have h1 : P Aᶜ + ENNReal.ofReal (1 - δ) ≤ ENNReal.ofReal δ + ENNReal.ofReal (1 - δ) := by
    calc P Aᶜ + ENNReal.ofReal (1 - δ) ≤ P Aᶜ + P A := by gcongr
      _ = P univ := by rw [add_comm]; exact measure_add_measure_compl hA
      _ = 1 := measure_univ
      _ = ENNReal.ofReal δ + ENNReal.ofReal (1 - δ) := by
          rw [add_comm, ← ENNReal.ofReal_add (by linarith) hδ]
          norm_num
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top h1

/-- Grid boxes of mesh `h > 0` are monotone in the integer endpoints. -/
lemma gridBox_subset_gridBox_of_le {h : ℝ} (hh : 0 < h) {P₁ P₂ Q₁ Q₂ a₁ a₂ b₁ b₂ : ℤ}
    (h1 : P₁ ≤ a₁) (h2 : a₂ ≤ P₂) (h3 : Q₁ ≤ b₁) (h4 : b₂ ≤ Q₂) :
    gridBox h a₁ a₂ b₁ b₂ ⊆ gridBox h P₁ P₂ Q₁ Q₂ := by
  unfold gridBox
  intro z hz
  obtain ⟨hr, hi⟩ := Complex.mem_reProdIm.1 hz
  have c1 : (P₁ : ℝ) * h ≤ (a₁ : ℝ) * h := mul_le_mul_of_nonneg_right (by exact_mod_cast h1) hh.le
  have c2 : (a₂ : ℝ) * h ≤ (P₂ : ℝ) * h := mul_le_mul_of_nonneg_right (by exact_mod_cast h2) hh.le
  have c3 : (Q₁ : ℝ) * h ≤ (b₁ : ℝ) * h := mul_le_mul_of_nonneg_right (by exact_mod_cast h3) hh.le
  have c4 : (b₂ : ℝ) * h ≤ (Q₂ : ℝ) * h := mul_le_mul_of_nonneg_right (by exact_mod_cast h4) hh.le
  exact Complex.mem_reProdIm.2 ⟨⟨le_trans c1 hr.1, le_trans hr.2 c2⟩, ⟨le_trans c3 hi.1, le_trans hi.2 c4⟩⟩

/-- A closed dyadic square of level `N` is the grid box of mesh `2^{-(N+3)}` with cell endpoints `j 2^3`, `(j+1) 2^3`. -/
lemma closedDyadicSquare_eq_gridBox_pow3 (N j k : ℤ) :
    closedDyadicSquare N j k = gridBox ((2 : ℝ) ^ (-(N + 3))) (j * 2 ^ 3) ((j + 1) * 2 ^ 3)
      (k * 2 ^ 3) ((k + 1) * 2 ^ 3) :=
  closedDyadicSquare_eq_gridBox N j k 3

/-- A closed dyadic square is a closed rectangle. -/
lemma isClosedRectangle_closedDyadicSquare (n j k : ℤ) : IsClosedRectangle (closedDyadicSquare n j k) := by
  unfold IsClosedRectangle closedDyadicSquare
  have hpos : (0 : ℝ) < 2 ^ (-n) := by positivity
  exact ⟨(j : ℝ) * 2 ^ (-n), ((j : ℝ) + 1) * 2 ^ (-n), (k : ℝ) * 2 ^ (-n), ((k : ℝ) + 1) * 2 ^ (-n),
    mul_lt_mul_of_pos_right (lt_add_one _) hpos, mul_lt_mul_of_pos_right (lt_add_one _) hpos, rfl⟩

/-- Twice the half of a nonnegative real is itself, in the extended nonnegative reals. -/
lemma two_mul_ofReal_half (C : ℝ) : 2 * ENNReal.ofReal (C / 2) = ENNReal.ofReal C := by
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

end HarmonicBalls
