import Mathlib

/-!
# Tiles, expanded squares and parity classes (Lemma 11.12 replacement, Theorem 2)

Deterministic geometry of the proof of Theorem 2 of the written proof. The square `S_0` is tiled by closed squares of side `ℓ`; each tile `S` has the concentric closed square
`H_S` of side `3ℓ/2`; the tiles are split into four classes by the parities of their two indices. Within one class the
expanded squares have pairwise disjoint closures, and some class carries at least a quarter of the total weight.
-/

namespace FirstPassS11i

open Set

/-- The closed tile of side `ℓ` with lower-left corner `ℓ (i, j)`, for `(i, j) ∈ ℤ²`. -/
def tileCore (ℓ : ℝ) (i j : ℤ) : Set ℂ :=
  {z | (i : ℝ) * ℓ ≤ z.re ∧ z.re ≤ ((i : ℝ) + 1) * ℓ ∧ (j : ℝ) * ℓ ≤ z.im ∧ z.im ≤ ((j : ℝ) + 1) * ℓ}

/-- The expanded square `H_S` of the tile `S = tileCore ℓ i j`: the concentric closed square of side `3ℓ/2`. -/
def tileExpanded (ℓ : ℝ) (i j : ℤ) : Set ℂ :=
  {z | ((i : ℝ) + 1 / 2) * ℓ - 3 * ℓ / 4 ≤ z.re ∧ z.re ≤ ((i : ℝ) + 1 / 2) * ℓ + 3 * ℓ / 4 ∧
    ((j : ℝ) + 1 / 2) * ℓ - 3 * ℓ / 4 ≤ z.im ∧ z.im ≤ ((j : ℝ) + 1 / 2) * ℓ + 3 * ℓ / 4}

/-- Parity class of the tile `(i, j)`: the two index parities (the four classes of Theorem 2). -/
def tileClass (i j : ℤ) : ℤ × ℤ := (i % 2, j % 2)

/-- Within one parity class the expanded squares have disjoint closures: two distinct tiles of the same class have
indices differing by at least `2` in some coordinate, and the expanded squares have half-width `3ℓ/4` around centres
spaced `ℓ` apart per index step. -/
theorem tileExpanded_disjoint {ℓ : ℝ} (hℓ : 0 < ℓ) {i j i' j' : ℤ}
    (hc : tileClass i j = tileClass i' j') (hne : (i, j) ≠ (i', j')) :
    Disjoint (tileExpanded ℓ i j) (tileExpanded ℓ i' j') := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨h1, h2, h3, h4⟩ := hz
  obtain ⟨h1', h2', h3', h4'⟩ := hz'
  have hi_up : ((i : ℝ) - i') * ℓ < 2 * ℓ := by linarith
  have hi_lo : -(2 * ℓ) < ((i : ℝ) - i') * ℓ := by linarith
  have hj_up : ((j : ℝ) - j') * ℓ < 2 * ℓ := by linarith
  have hj_lo : -(2 * ℓ) < ((j : ℝ) - j') * ℓ := by linarith
  have hi2 : (i : ℝ) - i' < 2 := lt_of_mul_lt_mul_right hi_up hℓ.le
  have hi3 : -2 < (i : ℝ) - i' := lt_of_mul_lt_mul_right (by linarith) hℓ.le
  have hj2 : (j : ℝ) - j' < 2 := lt_of_mul_lt_mul_right hj_up hℓ.le
  have hj3 : -2 < (j : ℝ) - j' := lt_of_mul_lt_mul_right (by linarith) hℓ.le
  have hi4 : i - i' < 2 := by exact_mod_cast hi2
  have hi5 : -2 < i - i' := by exact_mod_cast hi3
  have hj4 : j - j' < 2 := by exact_mod_cast hj2
  have hj5 : -2 < j - j' := by exact_mod_cast hj3
  simp only [tileClass, Prod.mk.injEq] at hc
  obtain ⟨hc1, hc2⟩ := hc
  have e1 : i = i' := by omega
  have e2 : j = j' := by omega
  exact hne (by rw [e1, e2])

/-- Pairwise disjointness of the expanded squares of one parity class of a finite family of tiles. -/
theorem tileExpanded_pairwiseDisjoint_class {ℓ : ℝ} (hℓ : 0 < ℓ) (F : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    (↑(F.filter (fun p => tileClass p.1 p.2 = c)) : Set (ℤ × ℤ)).PairwiseDisjoint
      (fun p : ℤ × ℤ => tileExpanded ℓ p.1 p.2) := by
  intro p hp q hq hpq
  simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
  have hc : tileClass p.1 p.2 = tileClass q.1 q.2 := by rw [hp.2, hq.2]
  exact tileExpanded_disjoint hℓ hc (by simpa using hpq)

/-- Pigeonhole over the four parity classes: for a finite family of tiles with nonnegative weights, some class
carries at least a quarter of the total weight. -/
theorem exists_class_sum_ge (F : Finset (ℤ × ℤ)) (w : ℤ × ℤ → ℝ) :
    ∃ c ∈ (Finset.Ico (0 : ℤ) 2 ×ˢ Finset.Ico (0 : ℤ) 2),
      (∑ p ∈ F, w p) / 4 ≤ ∑ p ∈ F.filter (fun p => tileClass p.1 p.2 = c), w p := by
  classical
  set C := (Finset.Ico (0 : ℤ) 2 ×ˢ Finset.Ico (0 : ℤ) 2) with hCdef
  have hmaps : ∀ p ∈ F, tileClass p.1 p.2 ∈ C := by
    intro p _
    simp only [hCdef, tileClass, Finset.mem_product, Finset.mem_Ico]
    omega
  have hsum : ∑ c ∈ C, ∑ p ∈ F.filter (fun p => tileClass p.1 p.2 = c), w p = ∑ p ∈ F, w p :=
    Finset.sum_fiberwise_of_maps_to hmaps w
  have hcard : C.card = 4 := by
    rw [hCdef, Finset.card_product, Int.card_Ico]
    rfl
  by_contra hcon
  push Not at hcon
  have hlt : ∑ c ∈ C, ∑ p ∈ F.filter (fun p => tileClass p.1 p.2 = c), w p <
      ∑ c ∈ C, (∑ p ∈ F, w p) / 4 :=
    Finset.sum_lt_sum_of_nonempty ⟨(0, 0), by simp [hCdef]⟩ hcon
  rw [hsum, Finset.sum_const, hcard, nsmul_eq_mul] at hlt
  push_cast at hlt
  linarith

end FirstPassS11i
