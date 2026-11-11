import HarmonicBalls.Proofs.Sec11.DyadicParitySquares
import HarmonicBalls.Defs.LBM

/-! # A closed square tiled by a finite grid -/

namespace HarmonicBalls
open Set

/-- A closed interval with natural length is covered by its unit intervals,
including the right endpoint. -/
theorem exists_unit_interval_index (N : ℕ) (hN : 0 < N) (x : ℝ)
    (hx0 : 0 ≤ x) (hxN : x ≤ N) :
    ∃ i : Fin N, (i.val : ℝ) ≤ x ∧ x ≤ (i.val : ℝ) + 1 := by
  by_cases hlt : x < N
  · have hf : ⌊x⌋₊ < N := (Nat.floor_lt hx0).2 hlt
    exact ⟨⟨⌊x⌋₊, hf⟩, Nat.floor_le hx0, (Nat.lt_floor_add_one x).le⟩
  · have hEq : x = N := le_antisymm hxN (le_of_not_gt hlt)
    have hn : N - 1 < N := by omega
    refine ⟨⟨N - 1, hn⟩, ?_⟩
    have hadd : N - 1 + 1 = N := by omega
    have hadd' : ((N - 1 : ℕ) : ℝ) + 1 = N := by exact_mod_cast hadd
    rw [hEq]
    constructor <;> linarith

/-- Each point of a closed square of side `N*r` belongs to one of the
`N²` closed grid squares of side `r`. -/
theorem closed_square_subset_grid_union (N : ℕ) (hN : 0 < N)
    (r : ℝ) (hr : 0 < r) :
    {x : ℝ × ℝ | 0 ≤ x.1 ∧ x.1 ≤ N * r ∧ 0 ≤ x.2 ∧ x.2 ≤ N * r} ⊆
      ⋃ i : Fin N × Fin N, gridSquare r i := by
  intro x hx
  have hx1 : 0 ≤ x.1 / r := div_nonneg hx.1 hr.le
  have hx2 : 0 ≤ x.2 / r := div_nonneg hx.2.2.1 hr.le
  have hx1N : x.1 / r ≤ N := (div_le_iff₀ hr).2 hx.2.1
  have hx2N : x.2 / r ≤ N := (div_le_iff₀ hr).2 hx.2.2.2
  obtain ⟨i, hi1, hi2⟩ := exists_unit_interval_index N hN (x.1 / r) hx1 hx1N
  obtain ⟨j, hj1, hj2⟩ := exists_unit_interval_index N hN (x.2 / r) hx2 hx2N
  apply mem_iUnion.mpr
  refine ⟨(i, j), ?_⟩
  exact ⟨(le_div_iff₀ hr).1 hi1, (div_le_iff₀ hr).1 hi2,
    (le_div_iff₀ hr).1 hj1, (div_le_iff₀ hr).1 hj2⟩

/-- The four parity classes cover the closed grid square. -/
theorem closed_square_subset_grid_classes (N : ℕ) (hN : 0 < N)
    (r : ℝ) (hr : 0 < r) :
    {x : ℝ × ℝ | 0 ≤ x.1 ∧ x.1 ≤ N * r ∧ 0 ≤ x.2 ∧ x.2 ≤ N * r} ⊆
      ⋃ j : Fin 4, gridSquareClass (N := N) r j :=
  (closed_square_subset_grid_union N hN r hr).trans (gridSquare_union_subset_classes r)

/-- Coordinates relative to the lower-left corner of a complex square. -/
def squareCoordinates (a z : ℂ) : ℝ × ℝ := (z.re - a.re, z.im - a.im)

/-- A complex grid square, expressed in coordinates relative to `a`. -/
def complexGridSquare {N : ℕ} (a : ℂ) (r : ℝ) (i : Fin N × Fin N) : Set ℂ :=
  squareCoordinates a ⁻¹' gridSquare r i

/-- A complex enlarged grid square of side `7r/4`. -/
def complexEnlargedGridSquare {N : ℕ} (a : ℂ) (r : ℝ) (i : Fin N × Fin N) : Set ℂ :=
  squareCoordinates a ⁻¹' enlargedGridSquare r i

/-- Four complex parity classes cover the closed square with lower-left
corner `a` and side `N*r`. -/
theorem complex_closed_square_subset_grid_classes
    (a : ℂ) (N : ℕ) (hN : 0 < N) (r : ℝ) (hr : 0 < r) :
    closedSquare a (N * r) ⊆
      ⋃ j : Fin 4, squareCoordinates a ⁻¹' gridSquareClass (N := N) r j := by
  intro z hz
  have hcoord : squareCoordinates a z ∈
      {x : ℝ × ℝ | 0 ≤ x.1 ∧ x.1 ≤ N * r ∧ 0 ≤ x.2 ∧ x.2 ≤ N * r} := by
    simp only [closedSquare, Complex.mem_reProdIm, mem_Icc] at hz
    simp only [squareCoordinates, mem_ofPred_eq]
    rcases hz with ⟨⟨h1, h2⟩, h3, h4⟩
    constructor <;> [linarith; constructor <;> [linarith; constructor <;> linarith]]
  have := closed_square_subset_grid_classes N hN r hr hcoord
  simpa only [mem_iUnion, mem_preimage] using this

/-- A fixed closed square is covered at every dyadic subdivision scale. -/
theorem complex_closed_square_subset_dyadic_classes
    (a : ℂ) (L : ℝ) (hL : 0 < L) (n : ℕ) :
    closedSquare a L ⊆ ⋃ j : Fin 4,
      squareCoordinates a ⁻¹' gridSquareClass (N := 2 ^ n) (L / 2 ^ n) j := by
  have hN : 0 < 2 ^ n := by positivity
  have hr : 0 < L / (2 : ℝ) ^ n := by positivity
  have h := complex_closed_square_subset_grid_classes a (2 ^ n) hN
    (L / (2 : ℝ) ^ n) hr
  simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_div_cancel₀ _ (by positivity : (2 : ℝ) ^ n ≠ 0)] using h


/-- Distinct complex enlarged squares in one parity class are disjoint. -/
theorem complex_enlarged_grid_squares_disjoint {N : ℕ} (a : ℂ) (r : ℝ) (hr : 0 < r)
    (i j : Fin N × Fin N) (hpar : squareParity i = squareParity j) (hne : i ≠ j) :
    Disjoint (complexEnlargedGridSquare a r i) (complexEnlargedGridSquare a r j) :=
  (enlarged_grid_squares_disjoint r hr i j hpar hne).preimage (squareCoordinates a)


end HarmonicBalls
