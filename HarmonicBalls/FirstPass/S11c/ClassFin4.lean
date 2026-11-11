import HarmonicBalls.FirstPass.S11c.Classes

/-!
# Proposition 11.10, the four classes indexed by `Fin 4`

The class selection of the printed proof of `lemma:mass-diam` (paper lines 3091-3112) and
`Assembly.exists_class_and_good_set` index the four parity classes `(j mod 2, k mod 2) ∈ {0,1}²` by `Fin 4`. This file
defines the class `classFin4 i` (index `i = 2p + q`) and shows that the square `[P₁ h, P₂ h] × [Q₁ h, Q₂ h]` is covered by
the four classes, using `Classes.gridS1_subset_classes`.
-/

open Set

namespace HarmonicBalls

/-- The class `i ∈ Fin 4` of the grid cells of mesh `h` inside the box `[P₁, P₂] × [Q₁, Q₂]`: the cells with parities
`(i / 2, i % 2)` of their indices. -/
def classFin4 (h : ℝ) (P₁ P₂ Q₁ Q₂ : ℤ) (i : Fin 4) : Set ℂ :=
  gridClassCells h {j : ℤ | j % 2 = (((i : ℕ) / 2 : ℕ) : ℤ) ∧ P₁ ≤ 8 * j ∧ 8 * j + 8 ≤ P₂}
    {k : ℤ | k % 2 = (((i : ℕ) % 2 : ℕ) : ℤ) ∧ Q₁ ≤ 8 * k ∧ 8 * k + 8 ≤ Q₂}

/-- The square `[P₁ h, P₂ h] × [Q₁ h, Q₂ h]` (with endpoints divisible by eight, of width at least sixteen) is covered by
the four classes. -/
lemma square_subset_iUnion_classFin4 {h : ℝ} (hh : 0 < h) {P₁ P₂ Q₁ Q₂ : ℤ} (hP₁ : P₁ % 8 = 0) (hP₂ : P₂ % 8 = 0)
    (hQ₁ : Q₁ % 8 = 0) (hQ₂ : Q₂ % 8 = 0) (hP : P₁ + 16 ≤ P₂) (hQ : Q₁ + 16 ≤ Q₂) :
    Icc ((P₁ : ℝ) * h) ((P₂ : ℝ) * h) ×ℂ Icc ((Q₁ : ℝ) * h) ((Q₂ : ℝ) * h) ⊆
      ⋃ i : Fin 4, classFin4 h P₁ P₂ Q₁ Q₂ i := by
  intro z hz
  have hcov := gridS1_subset_classes hh hP₁ hP₂ hQ₁ hQ₂ hP hQ hz
  simp only [mem_iUnion, mem_insert_iff, mem_singleton_iff] at hcov
  obtain ⟨p, hp, q, hq, hzc⟩ := hcov
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact mem_iUnion.2 ⟨0, by simpa [classFin4] using hzc⟩
  · exact mem_iUnion.2 ⟨1, by simpa [classFin4] using hzc⟩
  · exact mem_iUnion.2 ⟨2, by simpa [classFin4] using hzc⟩
  · exact mem_iUnion.2 ⟨3, by simpa [classFin4] using hzc⟩

end HarmonicBalls
