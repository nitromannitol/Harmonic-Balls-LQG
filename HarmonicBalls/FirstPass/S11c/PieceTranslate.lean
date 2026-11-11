import HarmonicBalls.FirstPass.S11c.Identify
import HarmonicBalls.FirstPass.S11c.Cover

/-!
# Proposition 11.10, the piece hypothesis of the pointwise shifted bound

`shifted_sup_le_of_good` (`FirstPass/S11c/Shifted.lean`) takes the internal diameters of the
enlarged pieces `gridBlock h j k ∩ gridBox` on the grid of mesh `h = 2^{-(N+3)}`. The small-cell event of the frozen
Proposition `DyadicCellDiamSmallFrozen` is stated with the Draft-level cells `enlargedDyadicCell N j k ∩ S₂`, with `S₂` a closed
dyadic square. This file identifies the two forms, so that the piece hypothesis of the pointwise bound follows from the
frozen small-cell event at the level `N` of the class cells.
-/

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicBalls

/-- The grid block of mesh `2^{-(N+3)}` is the enlarged dyadic cell of level `N`. -/
lemma gridBlock_eq_enlargedDyadicCell (N j k : ℤ) :
    gridBlock ((2 : ℝ) ^ (-(N + 3))) j k = enlargedDyadicCell N j k := by
  rw [enlargedDyadicCell_eq_block]
  rfl

/-- The piece hypothesis `hDP` of `shifted_sup_le_of_good`, from the small-cell diameter bound for the enlarged dyadic
cells inside the box `W = S₂`, for the class cells `Jx × Jy` of level `N`. -/
theorem hDP_of_enlarged_pieces {D : ℂ → ℂ → ℝ} {N : ℤ} {h : ℝ} {S₂ W : Set ℂ} {Jx Jy : Set ℤ} {ε : ℝ}
    (hh : h = (2 : ℝ) ^ (-(N + 3))) (hW : W = S₂)
    (hcell : ∀ p ∈ Jx ×ˢ Jy, closedDyadicSquare N p.1 p.2 ⊆ S₂)
    (hω : ∀ j k : ℤ, closedDyadicSquare N j k ⊆ S₂ → ∀ u ∈ enlargedDyadicCell N j k ∩ S₂,
      ∀ v ∈ enlargedDyadicCell N j k ∩ S₂,
        internalMetric D (enlargedDyadicCell N j k ∩ S₂) u v ≤ ENNReal.ofReal ε) :
    ∀ p : (Jx ×ˢ Jy : Set (ℤ × ℤ)), ∀ u ∈ gridBlock h p.1.1 p.1.2 ∩ W,
      ∀ v ∈ gridBlock h p.1.1 p.1.2 ∩ W,
        internalMetric D (gridBlock h p.1.1 p.1.2 ∩ W) u v ≤ ENNReal.ofReal ε := by
  intro p u hu v hv
  have hblk : gridBlock h p.1.1 p.1.2 = enlargedDyadicCell N p.1.1 p.1.2 := by
    rw [hh]
    exact gridBlock_eq_enlargedDyadicCell N p.1.1 p.1.2
  rw [hblk, hW] at hu hv ⊢
  exact hω p.1.1 p.1.2 (hcell p.1 p.2) u hu v hv

end HarmonicBalls
