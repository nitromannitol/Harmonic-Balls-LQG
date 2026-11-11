import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Interval.Set.Basic

/-!
# Proposition 11.10, grid bookkeeping of the exterior set

Work in units `h = 2^{-(N+3)}`, so that a level-`N` dyadic cell has side `8h`, and the enlargement
`Ŝ_j` of the level-`N` cell with index `j` (paper line 3010, side `2^{-N} + 2^{-N-2}` with the same centre) has
abscissa interval `[(8j-1)h, (8j+9)h]`. Integers `J` index the cells of one parity class inside `S₁`.

Lemmas here (all deterministic):
* `gridXs J h` is the union of the enlarged abscissa intervals; `gridAint J X` says that the unit cell
  `[Xh, (X+1)h]` lies inside one of them.
* a unit cell with `¬ gridAint J X` has open abscissa interval disjoint from `gridXs J h`;
* a point of an interval not covered by `gridXs J h` lies in a unit cell that is not `gridAint`;
* the parity structure gives free abscissae `(8j+12)h` and `(8j-4)h`, which yield the hub for the connectivity lemma.
-/

namespace HarmonicBalls

open Set

/-- The union of the abscissa intervals `[(8j-1)h, (8j+9)h]`, `j ∈ J`, of the enlarged level-`N` cells. -/
def gridXs (J : Set ℤ) (h : ℝ) : Set ℝ :=
  ⋃ j ∈ J, Icc ((8 * (j : ℝ) - 1) * h) ((8 * (j : ℝ) + 9) * h)

/-- The unit cell `[Xh, (X+1)h]` lies inside one enlarged abscissa interval (integer form). -/
def gridAint (J : Set ℤ) (X : ℤ) : Prop :=
  ∃ j ∈ J, 8 * j - 1 ≤ X ∧ X + 1 ≤ 8 * j + 9

lemma le_of_real_mul_le_int {h : ℝ} (hh : 0 < h) {a b : ℤ} (H : (a : ℝ) * h ≤ (b : ℝ) * h) : a ≤ b := by
  have : (a : ℝ) ≤ (b : ℝ) := le_of_mul_le_mul_right H hh
  exact_mod_cast this

lemma lt_of_real_mul_lt_int {h : ℝ} (hh : 0 < h) {a b : ℤ} (H : (a : ℝ) * h < (b : ℝ) * h) : a < b := by
  have : (a : ℝ) < (b : ℝ) := lt_of_mul_lt_mul_right H hh.le
  exact_mod_cast this

/-- A point of a unit cell with `gridAint` lies in `gridXs`. -/
lemma mem_gridXs_of_gridAint {J : Set ℤ} {h : ℝ} (hh : 0 < h) {X : ℤ} (hX : gridAint J X) {t : ℝ}
    (h1 : (X : ℝ) * h ≤ t) (h2 : t ≤ ((X : ℝ) + 1) * h) : t ∈ gridXs J h := by
  obtain ⟨j, hj, hA, hB⟩ := hX
  rw [gridXs, mem_iUnion₂]
  refine ⟨j, hj, ?_, ?_⟩
  · have hA' : ((8 * j - 1 : ℤ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast hA
    have : (8 * (j : ℝ) - 1) * h ≤ (X : ℝ) * h := mul_le_mul_of_nonneg_right (by push_cast at hA'; linarith) hh.le
    linarith
  · have hB' : (X : ℝ) + 1 ≤ ((8 * j + 9 : ℤ) : ℝ) := by exact_mod_cast hB
    have : ((X : ℝ) + 1) * h ≤ (8 * (j : ℝ) + 9) * h :=
      mul_le_mul_of_nonneg_right (by push_cast at hB'; linarith) hh.le
    linarith

/-- An open unit cell `(Xh, (X+1)h)` with `¬ gridAint J X` misses `gridXs J h`. -/
lemma not_mem_gridXs_of_not_gridAint {J : Set ℤ} {h : ℝ} (hh : 0 < h) {X : ℤ} (hX : ¬ gridAint J X)
    {t : ℝ} (h1 : (X : ℝ) * h < t) (h2 : t < ((X : ℝ) + 1) * h) : t ∉ gridXs J h := by
  intro ht
  rw [gridXs, mem_iUnion₂] at ht
  obtain ⟨j, hj, h3, h4⟩ := ht
  apply hX
  refine ⟨j, hj, ?_, ?_⟩
  · have h5 : ((8 * j - 1 : ℤ) : ℝ) * h < ((X + 1 : ℤ) : ℝ) * h := by
      push_cast
      linarith
    have := lt_of_real_mul_lt_int hh h5
    omega
  · have h5 : ((X : ℤ) : ℝ) * h < ((8 * j + 9 : ℤ) : ℝ) * h := by
      push_cast
      linarith
    have := lt_of_real_mul_lt_int hh h5
    omega

/-- Every point of `[A₁h, A₂h]` lies in a unit cell `[Xh, (X+1)h] ⊆ [A₁h, A₂h]`. -/
lemma exists_cell_in_box {h : ℝ} (hh : 0 < h) {A₁ A₂ : ℤ} (hA : A₁ + 1 ≤ A₂) {z : ℝ}
    (hz₁ : (A₁ : ℝ) * h ≤ z) (hz₂ : z ≤ (A₂ : ℝ) * h) :
    ∃ X : ℤ, A₁ ≤ X ∧ X + 1 ≤ A₂ ∧ (X : ℝ) * h ≤ z ∧ z ≤ ((X : ℝ) + 1) * h := by
  by_cases hlt : z < (A₂ : ℝ) * h
  · refine ⟨⌊z / h⌋, ?_, ?_, ?_, ?_⟩
    · apply Int.le_floor.2
      rw [le_div_iff₀ hh]
      linarith
    · have : ⌊z / h⌋ < A₂ := Int.floor_lt.2 (by rw [div_lt_iff₀ hh]; linarith)
      omega
    · exact (le_div_iff₀ hh).1 (Int.floor_le _)
    · exact ((div_lt_iff₀ hh).1 (Int.lt_floor_add_one _)).le
  · refine ⟨A₂ - 1, by omega, by omega, ?_, ?_⟩
    · push_cast
      have : z = (A₂ : ℝ) * h := le_antisymm hz₂ (not_lt.1 hlt)
      rw [this]
      nlinarith
    · push_cast
      have : z = (A₂ : ℝ) * h := le_antisymm hz₂ (not_lt.1 hlt)
      rw [this]
      nlinarith


/-- A point of `[A₁h, A₂h]` outside `gridXs J h` lies in a unit cell `[Xh, (X+1)h] ⊆ [A₁h, A₂h]` that is not
`gridAint`. -/
lemma exists_cell_of_not_mem_gridXs {J : Set ℤ} {h : ℝ} (hh : 0 < h) {A₁ A₂ : ℤ} (hA : A₁ + 1 ≤ A₂)
    {z : ℝ} (hz₁ : (A₁ : ℝ) * h ≤ z) (hz₂ : z ≤ (A₂ : ℝ) * h) (hz : z ∉ gridXs J h) :
    ∃ X : ℤ, A₁ ≤ X ∧ X + 1 ≤ A₂ ∧ ¬ gridAint J X ∧ (X : ℝ) * h ≤ z ∧ z ≤ ((X : ℝ) + 1) * h := by
  obtain ⟨X, hX₁, hX₂, hX₃, hX₄⟩ := exists_cell_in_box hh hA hz₁ hz₂
  refine ⟨X, hX₁, hX₂, ?_, hX₃, hX₄⟩
  intro hag
  exact hz (mem_gridXs_of_gridAint hh hag hX₃ hX₄)

/-- Free abscissae of the parity class: `(8j+12)h` is not in `gridXs J h` when all `j' ∈ J` have the parity of `j`. -/
lemma not_mem_gridXs_right {J : Set ℤ} {h : ℝ} (hh : 0 < h) {p j : ℤ} (hJ : ∀ j' ∈ J, j' % 2 = p)
    (hj : j % 2 = p) : (8 * (j : ℝ) + 12) * h ∉ gridXs J h := by
  intro ht
  rw [gridXs, mem_iUnion₂] at ht
  obtain ⟨j', hj', h3, h4⟩ := ht
  have hp := hJ j' hj'
  have a1 : ((8 * j' - 1 : ℤ) : ℝ) * h ≤ ((8 * j + 12 : ℤ) : ℝ) * h := by push_cast; linarith
  have a2 : ((8 * j + 12 : ℤ) : ℝ) * h ≤ ((8 * j' + 9 : ℤ) : ℝ) * h := by push_cast; linarith
  have b1 := le_of_real_mul_le_int hh a1
  have b2 := le_of_real_mul_le_int hh a2
  omega

/-- Free abscissae of the parity class: `(8j-4)h` is not in `gridXs J h`. -/
lemma not_mem_gridXs_left {J : Set ℤ} {h : ℝ} (hh : 0 < h) {p j : ℤ} (hJ : ∀ j' ∈ J, j' % 2 = p)
    (hj : j % 2 = p) : (8 * (j : ℝ) - 4) * h ∉ gridXs J h := by
  intro ht
  rw [gridXs, mem_iUnion₂] at ht
  obtain ⟨j', hj', h3, h4⟩ := ht
  have hp := hJ j' hj'
  have a1 : ((8 * j' - 1 : ℤ) : ℝ) * h ≤ ((8 * j - 4 : ℤ) : ℝ) * h := by push_cast; linarith
  have a2 : ((8 * j - 4 : ℤ) : ℝ) * h ≤ ((8 * j' + 9 : ℤ) : ℝ) * h := by push_cast; linarith
  have b1 := le_of_real_mul_le_int hh a1
  have b2 := le_of_real_mul_le_int hh a2
  omega

/-- The hub: a free abscissa in `[A₁h, A₂h]` for the parity class `p ∈ {0,1}` of the cells `j` with `P₁ ≤ 8j`,
`8j+8 ≤ P₂` (`P₁ ≡ 0 mod 8`, `P₂ ≥ P₁ + 16`). -/
theorem exists_free_abscissa {h : ℝ} (hh : 0 < h) {p P₁ P₂ A₁ A₂ : ℤ} (hp : p = 0 ∨ p = 1)
    (hP₁ : P₁ % 8 = 0) (hA₁ : A₁ ≤ P₁) (hP₂ : P₂ ≤ A₂) (hsz : P₁ + 16 ≤ P₂) (hA : A₁ + 16 ≤ A₂) :
    ∃ xh ∈ Icc ((A₁ : ℝ) * h) ((A₂ : ℝ) * h),
      xh ∉ gridXs {j : ℤ | j % 2 = p ∧ P₁ ≤ 8 * j ∧ 8 * j + 8 ≤ P₂} h := by
  have hJ : ∀ j' ∈ {j : ℤ | j % 2 = p ∧ P₁ ≤ 8 * j ∧ 8 * j + 8 ≤ P₂}, j' % 2 = p :=
    fun j' hj' => hj'.1
  have cast_le : ∀ a b : ℤ, a ≤ b → (a : ℝ) * h ≤ (b : ℝ) * h := fun a b H =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast H) hh.le
  obtain ⟨j, hjp, hjL, hjR⟩ : ∃ j : ℤ, j % 2 = p ∧ P₁ ≤ 8 * j ∧ 8 * j + 8 ≤ P₂ := by
    by_cases hpar : (P₁ / 8) % 2 = p
    · exact ⟨P₁ / 8, hpar, by omega, by omega⟩
    · exact ⟨P₁ / 8 + 1, by omega, by omega, by omega⟩
  by_cases hc : 8 * j + 12 ≤ A₂
  · refine ⟨(8 * (j : ℝ) + 12) * h, ⟨?_, ?_⟩, not_mem_gridXs_right hh hJ hjp⟩
    · have h1 : ((A₁ : ℤ) : ℝ) * h ≤ ((8 * j + 12 : ℤ) : ℝ) * h := cast_le _ _ (by omega)
      push_cast at h1
      linarith
    · have h1 : ((8 * j + 12 : ℤ) : ℝ) * h ≤ ((A₂ : ℤ) : ℝ) * h := cast_le _ _ hc
      push_cast at h1
      linarith
  · refine ⟨(8 * (j : ℝ) - 4) * h, ⟨?_, ?_⟩, not_mem_gridXs_left hh hJ hjp⟩
    · have h1 : ((A₁ : ℤ) : ℝ) * h ≤ ((8 * j - 4 : ℤ) : ℝ) * h := cast_le _ _ (by omega)
      push_cast at h1
      linarith
    · have h1 : ((8 * j - 4 : ℤ) : ℝ) * h ≤ ((A₂ : ℤ) : ℝ) * h := cast_le _ _ (by omega)
      push_cast at h1
      linarith

end HarmonicBalls
