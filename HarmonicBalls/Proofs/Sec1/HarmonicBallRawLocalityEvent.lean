import HarmonicBalls.Draft.Section1

/-! # Exact zero-time harmonic ball containment -/

namespace HarmonicBalls

open MeasureTheory Set

/-- The point-valued zero-time containment event is measurable in the raw
local field σ-algebra. -/
theorem measurableSet_harmonicBall_zero_containment {Ω : Type*}
    (α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (x : ℂ) (U : Set ℂ) :
    MeasurableSet[fieldSigmaAlgebra α₀ hC U] {_ω : Ω | ({x} : Set ℂ) ⊆ U} := by
  by_cases hx : x ∈ U
  · simpa only [singleton_subset_iff, hx, ofPred_true] using
      (@MeasurableSet.univ Ω (fieldSigmaAlgebra α₀ hC U))
  · simpa only [singleton_subset_iff, hx, ofPred_false] using
      (@MeasurableSet.empty Ω (fieldSigmaAlgebra α₀ hC U))

end HarmonicBalls
