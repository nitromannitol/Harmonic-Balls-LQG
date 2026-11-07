import HarmonicBalls.Proofs.Sec11.MassDiameterDyadicSelection

/-! # Parity classes of enlarged dyadic squares -/

namespace HarmonicBalls
open Set

/-- The parity class of a planar grid index, encoded by an element of `Fin 4`. -/
def squareParity {N : ℕ} (i : Fin N × Fin N) : Fin 4 :=
  ⟨i.1.val % 2 + 2 * (i.2.val % 2), by
    have h1 := Nat.mod_lt i.1.val (by omega : 0 < 2)
    have h2 := Nat.mod_lt i.2.val (by omega : 0 < 2)
    omega⟩

/-- The closed square concentric with a grid square of side `r` and
having side `7r/4`. -/
def enlargedGridSquare {N : ℕ} (r : ℝ) (i : Fin N × Fin N) : Set (ℝ × ℝ) :=
  {x | ((i.1.val : ℝ) - 3 / 8) * r ≤ x.1 ∧
       x.1 ≤ ((i.1.val : ℝ) + 11 / 8) * r ∧
       ((i.2.val : ℝ) - 3 / 8) * r ≤ x.2 ∧
       x.2 ≤ ((i.2.val : ℝ) + 11 / 8) * r}

/-- A closed square of side `r` in the coordinate grid. -/
def gridSquare {N : ℕ} (r : ℝ) (i : Fin N × Fin N) : Set (ℝ × ℝ) :=
  {x | (i.1.val : ℝ) * r ≤ x.1 ∧ x.1 ≤ ((i.1.val : ℝ) + 1) * r ∧
       (i.2.val : ℝ) * r ≤ x.2 ∧ x.2 ≤ ((i.2.val : ℝ) + 1) * r}

/-- The union of the grid squares belonging to one of the four parity classes. -/
def gridSquareClass {N : ℕ} (r : ℝ) (j : Fin 4) : Set (ℝ × ℝ) :=
  ⋃ i : Fin N × Fin N, if squareParity i = j then gridSquare r i else ∅

/-- Every grid square lies inside its concentric enlargement. -/
theorem gridSquare_subset_enlarged {N : ℕ} (r : ℝ) (hr : 0 ≤ r)
    (i : Fin N × Fin N) : gridSquare r i ⊆ enlargedGridSquare r i := by
  intro x hx
  rcases hx with ⟨h1, h2, h3, h4⟩
  change ((i.1.val : ℝ) - 3 / 8) * r ≤ x.1 ∧
       x.1 ≤ ((i.1.val : ℝ) + 11 / 8) * r ∧
       ((i.2.val : ℝ) - 3 / 8) * r ≤ x.2 ∧
       x.2 ≤ ((i.2.val : ℝ) + 11 / 8) * r
  constructor <;> [nlinarith; constructor <;> [nlinarith; constructor <;> nlinarith]]

/-- The four parity classes cover the union of all the grid squares. -/
theorem gridSquare_union_subset_classes {N : ℕ} (r : ℝ) :
    (⋃ i : Fin N × Fin N, gridSquare r i) ⊆ ⋃ j : Fin 4, gridSquareClass (N := N) r j := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  apply mem_iUnion.mpr
  refine ⟨squareParity i, ?_⟩
  change x ∈ ⋃ k : Fin N × Fin N, if squareParity k = squareParity i then gridSquare r k else ∅
  exact mem_iUnion.mpr ⟨i, by simpa using hi⟩

#print axioms gridSquare_subset_enlarged
#print axioms gridSquare_union_subset_classes

/-- Equal parity and distinct natural indices put the enlarged intervals
strictly apart. -/
theorem enlarged_grid_intervals_disjoint (r : ℝ) (hr : 0 < r)
    (i j : ℕ) (hpar : i % 2 = j % 2) (hne : i ≠ j) :
    Disjoint (Icc (((i : ℝ) - 3 / 8) * r) (((i : ℝ) + 11 / 8) * r))
      (Icc (((j : ℝ) - 3 / 8) * r) (((j : ℝ) + 11 / 8) * r)) := by
  apply disjoint_left.mpr
  intro x hx hy
  have hgap : i + 2 ≤ j ∨ j + 2 ≤ i := by omega
  rcases hgap with hij | hji
  · have hreal : (i : ℝ) + 2 ≤ j := by exact_mod_cast hij
    have hmul := mul_nonneg (show 0 ≤ (j : ℝ) - i - 2 by linarith) hr.le
    rcases hx with ⟨_, hxu⟩
    rcases hy with ⟨hyl, _⟩
    nlinarith
  · have hreal : (j : ℝ) + 2 ≤ i := by exact_mod_cast hji
    have hmul := mul_nonneg (show 0 ≤ (i : ℝ) - j - 2 by linarith) hr.le
    rcases hx with ⟨hxl, _⟩
    rcases hy with ⟨_, hyu⟩
    nlinarith

/-- The closures of side-`7r/4` enlargements of distinct squares in the
same parity class are disjoint. -/
theorem enlarged_grid_squares_disjoint {N : ℕ} (r : ℝ) (hr : 0 < r)
    (i j : Fin N × Fin N) (hpar : squareParity i = squareParity j) (hne : i ≠ j) :
    Disjoint (enlargedGridSquare r i) (enlargedGridSquare r j) := by
  have hv := congrArg Fin.val hpar
  simp only [squareParity] at hv
  have hi := Nat.mod_lt i.1.val (by omega : 0 < 2)
  have hj := Nat.mod_lt j.1.val (by omega : 0 < 2)
  have hi' := Nat.mod_lt i.2.val (by omega : 0 < 2)
  have hj' := Nat.mod_lt j.2.val (by omega : 0 < 2)
  have hp1 : i.1.val % 2 = j.1.val % 2 := by omega
  have hp2 : i.2.val % 2 = j.2.val % 2 := by omega
  have hcoord : i.1.val ≠ j.1.val ∨ i.2.val ≠ j.2.val := by
    by_contra hn
    push Not at hn
    apply hne
    exact Prod.ext (Fin.ext hn.1) (Fin.ext hn.2)
  apply disjoint_left.mpr
  intro x hx hy
  rcases hcoord with h1 | h2
  · exact (disjoint_left.mp (enlarged_grid_intervals_disjoint r hr _ _ hp1 h1))
      ⟨hx.1, hx.2.1⟩ ⟨hy.1, hy.2.1⟩
  · exact (disjoint_left.mp (enlarged_grid_intervals_disjoint r hr _ _ hp2 h2))
      ⟨hx.2.2.1, hx.2.2.2⟩ ⟨hy.2.2.1, hy.2.2.2⟩

#print axioms enlarged_grid_intervals_disjoint
#print axioms enlarged_grid_squares_disjoint
end HarmonicBalls
