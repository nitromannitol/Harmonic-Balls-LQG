import HarmonicBalls.Steps.Sec11.PinchPositiveDensity
import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-! # Measurable pinch-scale block frequencies

Joint measurability of each scale event implies joint measurability of the
finite block counts and their eventual lower bound. -/

namespace HarmonicBalls

open MeasureTheory Filter Set

/-- A finite block count is measurable when each event is measurable. -/
theorem measurable_blockEvent_ncard
    {X : Type*} [MeasurableSpace X] (E : ℕ → X → Prop)
    (hE : ∀ n, MeasurableSet {x | E n x}) (a b : ℕ) :
    Measurable (fun x => ({n : ℕ | a ≤ n ∧ n ≤ b ∧ E n x}.ncard : ℝ)) := by
  have hs : Measurable (fun x : X => {n : ℕ | a ≤ n ∧ n ≤ b ∧ E n x}) := by
    apply Measurable.of_eval
    intro n
    apply measurable_to_prop
    rw [preimage_singleton_true]
    change MeasurableSet {x : X | a ≤ n ∧ n ≤ b ∧ E n x}
    by_cases h : a ≤ n ∧ n ≤ b
    · simpa only [h.1, h.2, true_and] using hE n
    · have hset : {x : X | a ≤ n ∧ n ≤ b ∧ E n x} = ∅ := by
        ext x
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun hx => h ⟨hx.1, hx.2.1⟩
      rw [hset]
      exact MeasurableSet.empty
  exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_ncard.comp hs)

/-- An eventual lower bound on block counts is measurable. -/
theorem measurableSet_eventually_blockEvent_ncard
    {X : Type*} [MeasurableSpace X] (E : ℕ → X → Prop)
    (hE : ∀ n, MeasurableSet {x | E n x}) (q : ℝ) :
    MeasurableSet {x | ∀ᶠ N : ℕ in atTop, q * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ E n x}.ncard : ℝ)} := by
  have hblock (N : ℕ) : MeasurableSet {x : X | q * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ E n x}.ncard : ℝ)} :=
    measurableSet_le measurable_const (measurable_blockEvent_ncard E hE _ _)
  have heq : {x : X | ∀ᶠ N : ℕ in atTop, q * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ E n x}.ncard : ℝ)} =
      ⋃ K : ℕ, ⋂ N : ℕ, {x : X | K ≤ N → q * N ≤
        ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ E n x}.ncard : ℝ)} := by
    ext x
    simp only [eventually_atTop, mem_ofPred_eq, mem_iUnion, mem_iInter]
  rw [heq]
  apply MeasurableSet.iUnion
  intro K
  apply MeasurableSet.iInter
  intro N
  by_cases h : K ≤ N
  · simpa only [h, true_implies] using hblock N
  · simpa only [h, false_implies, ofPred_true] using (MeasurableSet.univ : MeasurableSet (univ : Set X))

/-- The eventual pinch-scale density event is jointly measurable if the
individual pinch-scale events are jointly measurable. -/
theorem measurableSet_eventually_pinchPointEvent_block_density
    {Ω : Type*} [MeasurableSpace Ω] (μ : Ω → Measure ℂ)
    (D : Ω → ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M q : ℝ)
    (hE : ∀ n : ℕ, MeasurableSet {x : Ω × ℂ |
      pinchPointEvent (μ x.1) (D x.1) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) x.2}) :
    MeasurableSet {x : Ω × ℂ | ∀ᶠ N : ℕ in atTop, q * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEvent (μ x.1) (D x.1) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) x.2}.ncard : ℝ)} :=
  measurableSet_eventually_blockEvent_ncard _ hE q

#print axioms measurable_blockEvent_ncard
#print axioms measurableSet_eventually_pinchPointEvent_block_density

end HarmonicBalls
