import HarmonicBalls.Draft.Section1

/-! # Transport of harmonic ball families at positive times -/

namespace HarmonicBalls

open MeasureTheory Set

/-- The conditions on a harmonic ball family depend only on its positive-time values. -/
theorem SatisfiesHarmonicBallConditions.congr {μ : Measure ℂ} {Λ Λ' : ℝ → Set ℂ}
    {z : ℂ} (h : SatisfiesHarmonicBallConditions μ Λ z)
    (heq : EqOn Λ Λ' (Ioi 0)) : SatisfiesHarmonicBallConditions μ Λ' z where
  measure_eq t ht := by rw [← heq ht]; exact h.measure_eq t ht
  measure_frontier t ht := by rw [← heq ht]; exact h.measure_frontier t ht
  isRegularOpen t ht := by rw [← heq ht]; exact h.isRegularOpen t ht
  isBounded t ht := by rw [← heq ht]; exact h.isBounded t ht
  isConnected t ht := by rw [← heq ht]; exact h.isConnected t ht
  mem t ht := by rw [← heq ht]; exact h.mem t ht
  monotoneOn := by
    intro s hs t ht hst
    rw [← heq hs, ← heq ht]
    exact h.monotoneOn hs ht hst
  hausdorffContinuousOn := by
    apply hausdorffContinuousOn_iff_continuousOn_closure.mpr
    apply (hausdorffContinuousOn_iff_continuousOn_closure.mp h.hausdorffContinuousOn).congr
    intro t ht
    dsimp only
    rw [← heq ht]
  iInter_eq := by
    have hinter : (⋂ t ∈ Ioi (0 : ℝ), Λ' t) = ⋂ t ∈ Ioi (0 : ℝ), Λ t := by
      ext x
      simp only [mem_iInter]
      constructor <;> intro hx t ht
      · rw [heq ht]; exact hx t ht
      · rw [← heq ht]; exact hx t ht
    rw [hinter, h.iInter_eq]

/-- A harmonic ball family remains one after changing its nonpositive-time values. -/
theorem IsHarmonicBallFamily.congr {μ : Measure ℂ} {Λ Λ' : ℝ → Set ℂ} {z : ℂ}
    (h : IsHarmonicBallFamily μ Λ z) (heq : EqOn Λ Λ' (Ioi 0)) :
    IsHarmonicBallFamily μ Λ' z := by
  refine ⟨?_, h.2.congr heq⟩
  intro t ht
  rw [← heq ht]
  exact h.1 t ht

end HarmonicBalls
