import HarmonicBalls.Proofs.Sec6.GoodAnnulusThreshold

/-!
# Positive recurrence from scale-invariant marginals

The fine-support argument for the good-annulus estimate uses that positive random ratios
with the same one-scale distribution remain bounded away from zero infinitely often.
No independence between scales is required (E19 route (b), Section 1.3(A)).
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter
open scoped ENNReal

/-- A sequence of positive random variables with identical lower-tail probabilities is
frequently bounded below by a positive random constant. -/
theorem ae_frequently_pos_of_equal_lower_tails
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : ℕ → Ω → ℝ) (hX : Measurable (X 0)) (hpos : ∀ᵐ ω ∂P, 0 < X 0 ω)
    (hlaw : ∀ n : ℕ, ∀ a : ℝ, P {ω | X n ω < a} = P {ω | X 0 ω < a}) :
    ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, ∃ n ≥ N, a ≤ X n ω := by
  classical
  apply ae_iff.2
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro δ hδ _
  simp only [bot_eq_zero, zero_add]
  have hδ' : (0 : ℝ≥0∞) < δ := by exact_mod_cast hδ
  obtain ⟨a, ha, hsmall⟩ := exists_small_threshold P hX hpos hδ'
  let B : ℕ → Set Ω := fun N => ⋂ n ≥ N, {ω | X n ω < a}
  have hmono : Monotone B := by
    intro i j hij ω hω
    simp only [B, mem_iInter, mem_ofPred_eq] at hω ⊢
    exact fun n hn => hω n (hij.trans hn)
  have hsub : {ω | ¬ ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n ≥ N, c ≤ X n ω} ⊆ ⋃ N, B N := by
    intro ω hω
    have hnot : ¬ ∀ N : ℕ, ∃ n ≥ N, a ≤ X n ω := by
      intro h
      exact hω ⟨a, ha.1, h⟩
    push Not at hnot
    obtain ⟨N, hN⟩ := hnot
    refine mem_iUnion.2 ⟨N, ?_⟩
    simp only [B, mem_iInter, mem_ofPred_eq]
    exact hN
  calc
    P {ω | ¬ ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n ≥ N, c ≤ X n ω} ≤ P (⋃ N, B N) := measure_mono hsub
    _ = ⨆ N, P (B N) := hmono.measure_iUnion
    _ ≤ δ := by
      refine iSup_le fun N => ?_
      have hBN : B N ⊆ {ω | X N ω < a} := by
        intro ω hω
        exact (mem_iInter.1 (mem_iInter.1 hω N) le_rfl)
      calc P (B N) ≤ P {ω | X N ω < a} := measure_mono hBN
        _ = P {ω | X 0 ω < a} := hlaw N a
        _ ≤ δ := hsmall

end HarmonicBalls.Section6
