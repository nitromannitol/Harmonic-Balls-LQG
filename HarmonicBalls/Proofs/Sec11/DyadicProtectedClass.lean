import HarmonicBalls.Proofs.Sec11.DyadicCoreGeometry

/-! # Protected dyadic mass classes -/

namespace HarmonicBalls
open Set

/-- A dyadic parity class is a closed subset of the square it tiles. -/
theorem dyadic_class_closed_and_subset (a : ℂ) (L : ℝ) (hL : 0 < L)
    (n : ℕ) (j : Fin 4) :
    IsClosed (squareCoordinates a ⁻¹' gridSquareClass (N := 2 ^ n) (L / 2 ^ n) j) ∧
    squareCoordinates a ⁻¹' gridSquareClass (N := 2 ^ n) (L / 2 ^ n) j ⊆ closedSquare a L := by
  let r : ℝ := L / (2 : ℝ) ^ n
  have hr : 0 < r := by dsimp [r]; positivity
  have hN : (2 : ℝ) ^ n * r = L := by dsimp [r]; field_simp
  rw [← union_complexGridSquare_eq_class]
  constructor
  · exact isClosed_iUnion_of_finite (fun i => isClosed_complexGridSquare a r i.1)
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    have hi1 : (i.1.1.val : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
      have h : i.1.1.val + 1 ≤ 2 ^ n := i.1.1.isLt
      exact_mod_cast h
    have hi2 : (i.1.2.val : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
      have h : i.1.2.val + 1 ≤ 2 ^ n := i.1.2.isLt
      exact_mod_cast h
    have hm1 := mul_nonneg (show 0 ≤ (2 : ℝ) ^ n - ((i.1.1.val : ℝ) + 1) by linarith) hr.le
    have hm2 := mul_nonneg (show 0 ≤ (2 : ℝ) ^ n - ((i.1.2.val : ℝ) + 1) by linarith) hr.le
    have hn1 : 0 ≤ (i.1.1.val : ℝ) := Nat.cast_nonneg _
    have hn2 : 0 ≤ (i.1.2.val : ℝ) := Nat.cast_nonneg _
    change (i.1.1.val : ℝ) * r ≤ z.re - a.re ∧
      z.re - a.re ≤ ((i.1.1.val : ℝ) + 1) * r ∧
      (i.1.2.val : ℝ) * r ≤ z.im - a.im ∧
      z.im - a.im ≤ ((i.1.2.val : ℝ) + 1) * r at hi
    simp only [closedSquare, Complex.mem_reProdIm, mem_Icc]
    rcases hi with ⟨h1, h2, h3, h4⟩
    constructor <;> [constructor <;> nlinarith; constructor <;> nlinarith]

#print axioms dyadic_class_closed_and_subset
end HarmonicBalls
