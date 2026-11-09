import HarmonicBalls.FirstPass.S11c.Classes

/-!
# Proposition 11.10, the class cells: closedness and containment in the square S₁ (fp-S11c, owner n1)

FIRST-PASS NEW (bookkeeping). In the printed proof of `lemma:mass-diam` (paper lines 3091-3112) the class `i` of the small
squares `S ∈ 𝒮_N^i` is a finite union of closed squares of mesh `h`, contained in `S₁`; the shift is zero on it, so the mass
of the class is unchanged, and the shift is zero on the unit circle. This file records that the class cell set indexed by
parities `(p, q)` is closed, and that it is contained in the square `[P₁ h, P₂ h] × [Q₁ h, Q₂ h]` of `S₁`.
-/

open Set Metric

namespace HarmonicBalls

/-- The indices `j` of the class cells inside `[P₁, P₂]` with parity `p` form a finite set. -/
lemma classIndex_finite (p P₁ P₂ : ℤ) : {j : ℤ | j % 2 = p ∧ P₁ ≤ 8 * j ∧ 8 * j + 8 ≤ P₂}.Finite :=
  (Set.finite_Icc (P₁ / 8 - 1) (P₂ / 8)).subset (by
    rintro j ⟨-, h1, h2⟩
    exact Set.mem_Icc.2 ⟨by omega, by omega⟩)

/-- The class cell set of parities `(p, q)` inside the box `[P₁, P₂] × [Q₁, Q₂]` is closed. -/
lemma isClosed_gridClassCells_index {h : ℝ} (p q P₁ P₂ Q₁ Q₂ : ℤ) :
    IsClosed (gridClassCells h {j : ℤ | j % 2 = p ∧ P₁ ≤ 8 * j ∧ 8 * j + 8 ≤ P₂}
      {k : ℤ | k % 2 = q ∧ Q₁ ≤ 8 * k ∧ 8 * k + 8 ≤ Q₂}) := by
  unfold gridClassCells
  refine (classIndex_finite p P₁ P₂).isClosed_biUnion fun j _ => ?_
  refine (classIndex_finite q Q₁ Q₂).isClosed_biUnion fun k _ => ?_
  exact (isClosed_Icc.preimage Complex.continuous_re).inter (isClosed_Icc.preimage Complex.continuous_im)

/-- The class cell set of parities `(p, q)` lies in the square `[P₁ h, P₂ h] × [Q₁ h, Q₂ h]`. -/
lemma gridClassCells_index_subset_square {h : ℝ} (hh : 0 < h) (p q P₁ P₂ Q₁ Q₂ : ℤ) :
    gridClassCells h {j : ℤ | j % 2 = p ∧ P₁ ≤ 8 * j ∧ 8 * j + 8 ≤ P₂}
      {k : ℤ | k % 2 = q ∧ Q₁ ≤ 8 * k ∧ 8 * k + 8 ≤ Q₂} ⊆
      Icc ((P₁ : ℝ) * h) ((P₂ : ℝ) * h) ×ℂ Icc ((Q₁ : ℝ) * h) ((Q₂ : ℝ) * h) := by
  intro z hz
  simp only [gridClassCells, mem_iUnion] at hz
  obtain ⟨j, ⟨-, hj2, hj3⟩, k, ⟨-, hk2, hk3⟩, hz⟩ := hz
  obtain ⟨hzr, hzi⟩ := Complex.mem_reProdIm.1 hz
  have hP1 : (P₁ : ℝ) ≤ 8 * (j : ℝ) := by exact_mod_cast hj2
  have hP2 : 8 * (j : ℝ) + 8 ≤ (P₂ : ℝ) := by exact_mod_cast hj3
  have hQ1 : (Q₁ : ℝ) ≤ 8 * (k : ℝ) := by exact_mod_cast hk2
  have hQ2 : 8 * (k : ℝ) + 8 ≤ (Q₂ : ℝ) := by exact_mod_cast hk3
  refine Complex.mem_reProdIm.2 ⟨⟨le_trans (mul_le_mul_of_nonneg_right hP1 hh.le) hzr.1,
    le_trans hzr.2 (mul_le_mul_of_nonneg_right hP2 hh.le)⟩,
    ⟨le_trans (mul_le_mul_of_nonneg_right hQ1 hh.le) hzi.1,
    le_trans hzi.2 (mul_le_mul_of_nonneg_right hQ2 hh.le)⟩⟩

end HarmonicBalls
