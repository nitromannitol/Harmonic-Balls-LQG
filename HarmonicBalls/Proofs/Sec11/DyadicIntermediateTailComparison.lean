import HarmonicBalls.Proofs.Sec11.DyadicIntermediateSquare

/-! # Comparison for dyadic internal-diameter estimates -/

namespace HarmonicBalls
open Set
open scoped ENNReal

/-- The internal diameter used for gluing is bounded by the diameter
measured within the closed intermediate square itself. -/
theorem dyadicIntermediateInternalDiameter_le_closedSquareDiameter
    {Ω : Type*} (D : Ω → ℂ → ℂ → ℝ) (a : ℂ) (L : ℝ) (hL : 0 < L)
    (n : ℕ) (i : Fin (2 ^ n) × Fin (2 ^ n)) (ω : Ω) :
    dyadicIntermediateInternalDiameter D a L n i ω ≤
      ⨆ x ∈ complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i,
        ⨆ y ∈ complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i,
          internalMetric (D ω) (complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i) x y := by
  have hr : 0 < L / (2 : ℝ) ^ n := by positivity
  unfold dyadicIntermediateInternalDiameter
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
  exact (internalMetric_anti (D ω) (complexIntermediateGridSquare_subset_open_enlarged a _ hr i)
    x y).trans (le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl))))

#print axioms dyadicIntermediateInternalDiameter_le_closedSquareDiameter
end HarmonicBalls
