import HarmonicBalls.Steps.Sec11.PinchLocalEvent
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-! # Common local representatives

Representatives constructed under the sum of two laws yield indicators that
agree with the original events under each law simultaneously.
-/

namespace HarmonicBalls

open Set MeasureTheory Filter

open Classical in
/-- Countably many local event representatives under the sum of two measures
produce a common locally measurable tail indicator under both measures. -/
theorem exists_common_local_tail_indicators
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P Q : Measure Ω)
    {m : MeasurableSpace Ω} (K : ℕ) (E : ℕ → Ω → Prop)
    (hE : ∀ k, K ≤ k → ∃ A : Set Ω, MeasurableSet[m] A ∧
      ∀ᵐ ω ∂(P + Q), (E k ω ↔ ω ∈ A)) :
    ∃ X : ℕ → Ω → ℝ, (∀ k, K ≤ k → Measurable[m] (X k)) ∧
      (∀ᵐ ω ∂P, ∀ k, K ≤ k → X k ω = if E k ω then 1 else 0) ∧
      (∀ᵐ ω ∂Q, ∀ k, K ≤ k → X k ω = if E k ω then 1 else 0) := by
  have hex (k : ℕ) : ∃ A : Set Ω, MeasurableSet[m] A ∧
      (K ≤ k → ∀ᵐ ω ∂(P + Q), (E k ω ↔ ω ∈ A)) := by
    by_cases hk : K ≤ k
    · obtain ⟨A, hA, heq⟩ := hE k hk
      exact ⟨A, hA, fun _ => heq⟩
    · exact ⟨∅, MeasurableSet.empty, fun h => (hk h).elim⟩
  let A (k : ℕ) := Classical.choose (hex k)
  have hA (k : ℕ) : MeasurableSet[m] (A k) := (Classical.choose_spec (hex k)).1
  have heq : ∀ᵐ ω ∂(P + Q), ∀ k, K ≤ k → (E k ω ↔ ω ∈ A k) := by
    rw [ae_all_iff]
    intro k
    by_cases hk : K ≤ k
    · filter_upwards [(Classical.choose_spec (hex k)).2 hk] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall (fun _ h => (hk h).elim)
  let X (k : ℕ) (ω : Ω) : ℝ := if ω ∈ A k then 1 else 0
  have hX (k : ℕ) : Measurable[m] (X k) := by
    let : MeasurableSpace Ω := m
    have hx : Measurable ((A k).indicator (fun _ : Ω => (1 : ℝ))) :=
      measurable_const.indicator (hA k)
    have he : (A k).indicator (fun _ : Ω => (1 : ℝ)) = X k := by
      funext ω
      by_cases h : ω ∈ A k <;> simp [X, Set.indicator, h]
    rw [← he]
    exact hx
  have hboth : ∀ᵐ ω ∂(P + Q), ∀ k, K ≤ k → X k ω = if E k ω then 1 else 0 := by
    filter_upwards [heq] with ω hω k hk
    simp only [X]
    split_ifs <;> simp_all
  exact ⟨X, fun k _ => hX k, (ae_add_measure_iff.mp hboth).1,
    (ae_add_measure_iff.mp hboth).2⟩

#print axioms exists_common_local_tail_indicators

end HarmonicBalls
