import HarmonicBalls.FirstPass.S11h.LocalEvents
import HarmonicBalls.Steps.Sec11.PinchInternalDiam

/-! # Closed endpoints in the local pinch certificates -/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- The internal diameter is unchanged by closing its endpoint set. -/
theorem IsEuclideanLengthMetric.internalDiam_closure_eq
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {δ : ℝ} (hδ : 0 < δ) (A : Set ℂ) :
    internalDiam D δ (closure A) = internalDiam D δ A := by
  have hnonneg (x y : ℂ) : 0 ≤ D x y := by
    have h := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at h
    linarith
  apply le_antisymm
  · unfold internalDiam at ⊢
    rw [thickening_closure]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
    exact hD.internalMetric_le_internalDiam_of_mem_closure hnonneg isOpen_thickening
      (closure_subset_thickening hδ A) Subset.rfl hx hy
  · exact internalDiam_le_closure D δ A

/-- The second local certificate agrees with the open-endpoint version. -/
theorem pinchSecondEventLocal_iff_of_lengthMetric
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {δ : ℝ} (hδ : 0 < δ)
    (μ : MeasureTheory.Measure ℂ) (U V : Set ℂ) (M : ℝ) :
    pinchSecondEventLocal μ D U V δ M ↔ pinchSecondEvent μ D U V δ M := by
  simp only [pinchSecondEventLocal, pinchSecondEvent, hD.internalDiam_closure_eq hδ V]

/-- The third local certificate agrees with the open-endpoint version. -/
theorem pinchThirdEventLocal_iff_of_lengthMetric
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {δ : ℝ} (hδ : 0 < δ) (V W : Set ℂ) :
    pinchThirdEventLocal D V W δ ↔ pinchThirdEvent D V W δ := by
  simp only [pinchThirdEventLocal, pinchThirdEvent, hD.internalDiam_closure_eq hδ _]

end HarmonicBalls
