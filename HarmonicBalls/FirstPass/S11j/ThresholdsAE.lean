import HarmonicBalls.FirstPass.S11j.Positivity

/-!
# First pass, Section 11: positive-probability thresholds, almost-everywhere measurable form (fp-S11j, owner n4)

The Measurable version `exists_thresholds_measure_pos` (`FirstPass/S11j/Positivity.lean:76`) is upgraded to
almost-everywhere measurable variables. Each variable is replaced by a measurable version; the positivity and
finiteness hypotheses transfer, and so does the event, since the two events agree almost everywhere. Pure measure
theory.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- The thresholds lemma for almost-everywhere measurable variables. -/
theorem exists_thresholds_measure_pos_of_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X₁ X₂ X₃ X₄ : Ω → ℝ≥0∞}
    (h₁ : AEMeasurable X₁ P) (h₂ : AEMeasurable X₂ P) (h₃ : AEMeasurable X₃ P) (h₄ : AEMeasurable X₄ P)
    (p₁ : ∀ᵐ ω ∂P, 0 < X₁ ω) (p₂ : ∀ᵐ ω ∂P, X₂ ω < ∞)
    (p₃ : ∀ᵐ ω ∂P, 0 < X₃ ω) (p₄ : ∀ᵐ ω ∂P, X₄ ω < ∞) :
    ∃ n k m l : ℕ, 0 < n ∧ 0 < k ∧
      0 < P {ω | (n : ℝ≥0∞)⁻¹ ≤ X₁ ω ∧ X₂ ω ≤ (m : ℝ≥0∞) ∧
        (k : ℝ≥0∞)⁻¹ ≤ X₃ ω ∧ X₄ ω ≤ (l : ℝ≥0∞)} := by
  obtain ⟨g₁, hg₁, e₁⟩ := h₁
  obtain ⟨g₂, hg₂, e₂⟩ := h₂
  obtain ⟨g₃, hg₃, e₃⟩ := h₃
  obtain ⟨g₄, hg₄, e₄⟩ := h₄
  have q₁ : ∀ᵐ ω ∂P, 0 < g₁ ω := by
    filter_upwards [p₁, e₁] with ω h hω
    rw [← hω]
    exact h
  have q₂ : ∀ᵐ ω ∂P, g₂ ω < ∞ := by
    filter_upwards [p₂, e₂] with ω h hω
    rw [← hω]
    exact h
  have q₃ : ∀ᵐ ω ∂P, 0 < g₃ ω := by
    filter_upwards [p₃, e₃] with ω h hω
    rw [← hω]
    exact h
  have q₄ : ∀ᵐ ω ∂P, g₄ ω < ∞ := by
    filter_upwards [p₄, e₄] with ω h hω
    rw [← hω]
    exact h
  obtain ⟨n, k, m, l, hn, hk, hpos⟩ :=
    exists_thresholds_measure_pos hg₁ hg₂ hg₃ hg₄ q₁ q₂ q₃ q₄
  refine ⟨n, k, m, l, hn, hk, ?_⟩
  have heq : {ω | (n : ℝ≥0∞)⁻¹ ≤ X₁ ω ∧ X₂ ω ≤ (m : ℝ≥0∞) ∧
      (k : ℝ≥0∞)⁻¹ ≤ X₃ ω ∧ X₄ ω ≤ (l : ℝ≥0∞)} =ᵐ[P]
      {ω | (n : ℝ≥0∞)⁻¹ ≤ g₁ ω ∧ g₂ ω ≤ (m : ℝ≥0∞) ∧
        (k : ℝ≥0∞)⁻¹ ≤ g₃ ω ∧ g₄ ω ≤ (l : ℝ≥0∞)} := by
    filter_upwards [e₁, e₂, e₃, e₄] with ω h1 h2 h3 h4
    simp [h1, h2, h3, h4]
  rw [measure_congr heq]
  exact hpos

#print axioms exists_thresholds_measure_pos_of_aemeasurable

end HarmonicBalls
