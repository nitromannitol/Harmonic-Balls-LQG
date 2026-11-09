import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.S11c.Exterior

/-!
# Proposition 11.10, identification of the dyadic data with the grid (fp-S11c, owner n1)

FIRST-PASS NEW. The Draft's dyadic squares and the frozen enlarged cells `enlargedDyadicCell` (Frozen/S11c.lean) are
rewritten in the unit `h = 2^{-(N+3)}` of the grid bookkeeping (`Grid.lean`, `Exterior.lean`):
* the level-`N` enlargement `Ŝ_{j,k}` is the block `[(8j-1)h, (8j+9)h] × [(8k-1)h, (8k+9)h]`
  (paper line 3010: side `2^{-N} + 2^{-N-2}`, same centre; `2^{-N} = 8h`, `2^{-N-2} = 2h`);
* a closed dyadic square of level `m` is a grid box with integer corners, `h = 2^{-(m+d)}`, `d` the level gap.
-/

namespace HarmonicBalls

open Set

lemma two_zpow_neg_eq_eight (N : ℤ) : (2 : ℝ) ^ (-N) = 8 * (2 : ℝ) ^ (-(N + 3)) := by
  have e : -N = -(N + 3) + 3 := by ring
  rw [e, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [show (2 : ℝ) ^ (3 : ℤ) = 8 by norm_num]
  ring

lemma two_zpow_neg_two_eq (N : ℤ) : (2 : ℝ) ^ (-N - 2) = 2 * (2 : ℝ) ^ (-(N + 3)) := by
  have e : -N - 2 = -(N + 3) + 1 := by ring
  rw [e, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  ring

/-- The enlarged level-`N` cell with index `(j, k)` is the block of the grid in the unit `h = 2^{-(N+3)}`. -/
theorem enlargedDyadicCell_eq_block (N j k : ℤ) :
    enlargedDyadicCell N j k =
      {z : ℂ | z.re ∈ Icc ((8 * (j : ℝ) - 1) * (2 : ℝ) ^ (-(N + 3))) ((8 * (j : ℝ) + 9) * (2 : ℝ) ^ (-(N + 3))) ∧
        z.im ∈ Icc ((8 * (k : ℝ) - 1) * (2 : ℝ) ^ (-(N + 3))) ((8 * (k : ℝ) + 9) * (2 : ℝ) ^ (-(N + 3)))} := by
  ext z
  simp only [enlargedDyadicCell, Set.mem_ofPred_eq]
  rw [two_zpow_neg_eq_eight N, two_zpow_neg_two_eq N]
  simp only [abs_sub_le_iff, mem_Icc]
  constructor
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- A closed dyadic square of level `m` is a grid box in the unit `h = 2^{-(m+d)}` with integer corners `j·2^d`. -/
theorem closedDyadicSquare_eq_gridBox (m j k : ℤ) (d : ℕ) :
    closedDyadicSquare m j k =
      gridBox ((2 : ℝ) ^ (-(m + d))) (j * 2 ^ d) ((j + 1) * 2 ^ d) (k * 2 ^ d) ((k + 1) * 2 ^ d) := by
  have e : (2 : ℝ) ^ (-m) = (2 : ℝ) ^ d * (2 : ℝ) ^ (-(m + d)) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  ext z
  simp only [closedDyadicSquare, gridBox, Complex.mem_reProdIm, mem_Icc, e]
  push_cast
  constructor
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
    exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
    exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

end HarmonicBalls
