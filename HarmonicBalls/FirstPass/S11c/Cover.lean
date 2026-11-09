import HarmonicBalls.FirstPass.S11c.Exterior

/-!
# Proposition 11.10, covering of the box by `K₁` and the enlarged blocks (fp-S11c, owner n1)

FIRST-PASS NEW. The covering hypothesis of the chain bound `internalMetric_le_three_pieces` (Chain.lean) for the
square `S₂`: the box `gridBox` is covered by the exterior set `K₁` and by the enlarged blocks `Ŝ_{j,k} ∩ S₂`, `j ∈ Jx`,
`k ∈ Jy`. The point outside `K₀ = box \ (Xs ×ℂ Ys)` lies in `Xs ×ℂ Ys`, which is the union of the enlarged blocks.
-/

namespace HarmonicBalls

open Set

/-- The enlarged block `Ŝ_{j,k}` of the level-`N` cell `(j, k)` in the unit `h`. -/
def gridBlock (h : ℝ) (j k : ℤ) : Set ℂ :=
  {z : ℂ | z.re ∈ Icc ((8 * (j : ℝ) - 1) * h) ((8 * (j : ℝ) + 9) * h) ∧
    z.im ∈ Icc ((8 * (k : ℝ) - 1) * h) ((8 * (k : ℝ) + 9) * h)}

/-- Covering: the box is covered by `K₁` and the enlarged blocks of the class. -/
theorem gridBox_subset_gridK1_union_blocks {h : ℝ} (hh : 0 < h) {Jx Jy : Set ℤ} {A₁ A₂ B₁ B₂ : ℤ}
    (hA : A₁ + 1 ≤ A₂) (hB : B₁ + 1 ≤ B₂) :
    gridBox h A₁ A₂ B₁ B₂ ⊆
      gridK1 h Jx Jy A₁ A₂ B₁ B₂ ∪ ⋃ p ∈ Jx ×ˢ Jy, gridBlock h p.1 p.2 := by
  intro z hz
  by_cases hE : z ∈ {z : ℂ | z.re ∈ gridXs Jx h ∧ z.im ∈ gridXs Jy h}
  · right
    obtain ⟨hx, hy⟩ := hE
    obtain ⟨j, hj, hzx⟩ := mem_iUnion₂.1 hx
    obtain ⟨k, hk, hzy⟩ := mem_iUnion₂.1 hy
    exact mem_iUnion₂.2 ⟨(j, k), ⟨hj, hk⟩, ⟨hzx, hzy⟩⟩
  · left
    exact gridK0_subset_gridK1 hh hA hB ⟨hz, hE⟩

end HarmonicBalls
