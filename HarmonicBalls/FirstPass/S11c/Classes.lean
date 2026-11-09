import HarmonicBalls.FirstPass.S11c.Exterior

/-!
# Proposition 11.10, parity classes of the level-`N` cells (fp-S11c, owner n1)

FIRST-PASS NEW. The class cells `U` of the paper's proof of `lemma:mass-diam` (corrected lines 3046-3055): the level-`N`
cells `[8jh, (8j+8)h] × [8kh, (8k+8)h]` of `S₁` split into four parity classes `(j mod 2, k mod 2)`. Lemmas:
* `gridK1_disjoint_gridClassCells`: the exterior set `K₁` misses every class cell (a unit cell that meets a class cell
  is inside the enlarged interval of that cell in both directions, hence not in the family);
* `gridS1_subset_classes`: the level-`N` cells of `S₁` are covered by the four classes.
-/

namespace HarmonicBalls

open Set

/-- The class cells: the level-`N` cells `[8jh, (8j+8)h] × [8kh, (8k+8)h]`, `j ∈ Jx`, `k ∈ Jy`. -/
def gridClassCells (h : ℝ) (Jx Jy : Set ℤ) : Set ℂ :=
  ⋃ j ∈ Jx, ⋃ k ∈ Jy, Icc (8 * (j : ℝ) * h) ((8 * (j : ℝ) + 8) * h) ×ℂ
    Icc (8 * (k : ℝ) * h) ((8 * (k : ℝ) + 8) * h)

lemma gridK1_disjoint_gridClassCells {h : ℝ} (hh : 0 < h) {Jx Jy : Set ℤ} {A₁ A₂ B₁ B₂ : ℤ} :
    Disjoint (gridK1 h Jx Jy A₁ A₂ B₁ B₂) (gridClassCells h Jx Jy) := by
  rw [Set.disjoint_left]
  intro z hzK hzU
  obtain ⟨p, hp, hzc⟩ := mem_iUnion₂.1 hzK
  simp only [gridClassCells, mem_iUnion₂] at hzU
  obtain ⟨j, hj, k, hk, hzj⟩ := hzU
  obtain ⟨-, -, -, -, hn⟩ := hp
  rw [mem_gridCell_iff] at hzc
  obtain ⟨⟨c1, c2⟩, ⟨c3, c4⟩⟩ := Complex.mem_reProdIm.1 hzj
  have a1 : (p.1 : ℝ) * h ≤ ((8 * j + 8 : ℤ) : ℝ) * h := by push_cast; linarith [hzc.1]
  have a2 : ((8 * j : ℤ) : ℝ) * h ≤ ((p.1 + 1 : ℤ) : ℝ) * h := by push_cast; linarith [hzc.2.1]
  have b1 : (p.2 : ℝ) * h ≤ ((8 * k + 8 : ℤ) : ℝ) * h := by push_cast; linarith [hzc.2.2.1]
  have b2 : ((8 * k : ℤ) : ℝ) * h ≤ ((p.2 + 1 : ℤ) : ℝ) * h := by push_cast; linarith [hzc.2.2.2]
  have e1 := le_of_real_mul_le_int hh a1
  have e2 := le_of_real_mul_le_int hh a2
  have f1 := le_of_real_mul_le_int hh b1
  have f2 := le_of_real_mul_le_int hh b2
  rcases hn with hn | hn
  · exact hn ⟨j, hj, by omega, by omega⟩
  · exact hn ⟨k, hk, by omega, by omega⟩

/-- The four parity classes cover the box `S₁ = [P₁h,P₂h] × [Q₁h,Q₂h]` (level-`N` cells of `S₁`): each point lies in a
level-`N` cell `[8Xh, (8X+8)h] × [8Yh, (8Y+8)h]` inside `S₁`, and `(X mod 2, Y mod 2) ∈ {0,1}²`. -/
lemma gridS1_subset_classes {h : ℝ} (hh : 0 < h) {P₁ P₂ Q₁ Q₂ : ℤ} (hP₁ : P₁ % 8 = 0) (hP₂ : P₂ % 8 = 0)
    (hQ₁ : Q₁ % 8 = 0) (hQ₂ : Q₂ % 8 = 0)
    (hP : P₁ + 16 ≤ P₂) (hQ : Q₁ + 16 ≤ Q₂) :
    Icc ((P₁ : ℝ) * h) ((P₂ : ℝ) * h) ×ℂ Icc ((Q₁ : ℝ) * h) ((Q₂ : ℝ) * h) ⊆
      ⋃ p ∈ ({0, 1} : Set ℤ), ⋃ q ∈ ({0, 1} : Set ℤ),
        gridClassCells h {j : ℤ | j % 2 = p ∧ P₁ ≤ 8 * j ∧ 8 * j + 8 ≤ P₂}
          {k : ℤ | k % 2 = q ∧ Q₁ ≤ 8 * k ∧ 8 * k + 8 ≤ Q₂} := by
  intro z hz
  obtain ⟨hzr, hzi⟩ := Complex.mem_reProdIm.1 hz
  have h8 : 0 < 8 * h := by linarith
  have eP1 : ((P₁ / 8 : ℤ) : ℝ) * (8 * h) = (P₁ : ℝ) * h := by
    have : (P₁ : ℝ) = 8 * ((P₁ / 8 : ℤ) : ℝ) := by exact_mod_cast (show P₁ = 8 * (P₁ / 8) by omega)
    rw [this]; ring
  have eP2 : ((P₂ / 8 : ℤ) : ℝ) * (8 * h) = (P₂ : ℝ) * h := by
    have : (P₂ : ℝ) = 8 * ((P₂ / 8 : ℤ) : ℝ) := by exact_mod_cast (show P₂ = 8 * (P₂ / 8) by omega)
    rw [this]; ring
  have eQ1 : ((Q₁ / 8 : ℤ) : ℝ) * (8 * h) = (Q₁ : ℝ) * h := by
    have : (Q₁ : ℝ) = 8 * ((Q₁ / 8 : ℤ) : ℝ) := by exact_mod_cast (show Q₁ = 8 * (Q₁ / 8) by omega)
    rw [this]; ring
  have eQ2 : ((Q₂ / 8 : ℤ) : ℝ) * (8 * h) = (Q₂ : ℝ) * h := by
    have : (Q₂ : ℝ) = 8 * ((Q₂ / 8 : ℤ) : ℝ) := by exact_mod_cast (show Q₂ = 8 * (Q₂ / 8) by omega)
    rw [this]; ring
  obtain ⟨X, hX1, hX2, hX3, hX4⟩ := exists_cell_in_box h8 (show P₁ / 8 + 1 ≤ P₂ / 8 by omega)
    (z := z.re) (by rw [eP1]; exact hzr.1) (by rw [eP2]; exact hzr.2)
  obtain ⟨Y, hY1, hY2, hY3, hY4⟩ := exists_cell_in_box h8 (show Q₁ / 8 + 1 ≤ Q₂ / 8 by omega)
    (z := z.im) (by rw [eQ1]; exact hzi.1) (by rw [eQ2]; exact hzi.2)
  have hXa : P₁ ≤ 8 * X := by omega
  have hXb : 8 * X + 8 ≤ P₂ := by omega
  have hYa : Q₁ ≤ 8 * Y := by omega
  have hYb : 8 * Y + 8 ≤ Q₂ := by omega
  refine mem_iUnion₂.2 ⟨X % 2, ?_, mem_iUnion₂.2 ⟨Y % 2, ?_, ?_⟩⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · simp only [gridClassCells, mem_iUnion₂]
    refine ⟨X, ⟨rfl, hXa, hXb⟩, Y, ⟨rfl, hYa, hYb⟩, ?_⟩
    refine Complex.mem_reProdIm.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · linarith [hX3]
    · linarith [hX4]
    · linarith [hY3]
    · linarith [hY4]

/-- The class cells lie in the box of `S₁`: each cell `[8jh, (8j+8)h]` with `P₁ ≤ 8j`, `8j+8 ≤ P₂` is inside `[P₁h, P₂h]`. -/
lemma gridClassCells_subset_box {h : ℝ} (hh : 0 < h) {p q P₁ P₂ Q₁ Q₂ : ℤ} :
    gridClassCells h {j : ℤ | j % 2 = p ∧ P₁ ≤ 8 * j ∧ 8 * j + 8 ≤ P₂}
        {k : ℤ | k % 2 = q ∧ Q₁ ≤ 8 * k ∧ 8 * k + 8 ≤ Q₂} ⊆ gridBox h P₁ P₂ Q₁ Q₂ := by
  intro z hz
  simp only [gridClassCells, mem_iUnion] at hz
  obtain ⟨j, ⟨-, hj1, hj2⟩, k, ⟨-, hk1, hk2⟩, hzc⟩ := hz
  obtain ⟨⟨c1, c2⟩, ⟨c3, c4⟩⟩ := Complex.mem_reProdIm.1 hzc
  have a1 : (P₁ : ℝ) * h ≤ (8 * (j : ℝ)) * h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast (show P₁ ≤ 8 * j from hj1)) hh.le
  have a2 : (8 * (j : ℝ) + 8) * h ≤ (P₂ : ℝ) * h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast (show 8 * j + 8 ≤ P₂ from hj2)) hh.le
  have b1 : (Q₁ : ℝ) * h ≤ (8 * (k : ℝ)) * h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast (show Q₁ ≤ 8 * k from hk1)) hh.le
  have b2 : (8 * (k : ℝ) + 8) * h ≤ (Q₂ : ℝ) * h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast (show 8 * k + 8 ≤ Q₂ from hk2)) hh.le
  exact Complex.mem_reProdIm.2 ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

end HarmonicBalls
