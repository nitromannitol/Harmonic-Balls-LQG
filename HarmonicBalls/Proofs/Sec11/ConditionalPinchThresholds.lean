import HarmonicBalls.Proofs.Sec11.ConditionalPositiveIntersection
import HarmonicBalls.Steps.Sec11.PinchThresholdSelection

/-! # Conditional threshold assembly for the second pinch event -/

namespace HarmonicBalls
open MeasureTheory Set Filter
open scoped ENNReal

/-- On a positive outside event, positive finite outside margins and positive
conditional probability of every strict inside threshold give a positive
intersection with both strict comparisons. -/
theorem positive_comparisons_of_conditional_thresholds
    {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) (A : Set Ω)
    (a b x y : Ω → ℝ≥0∞)
    (hA : MeasurableSet[m] A) (ha : @Measurable Ω ℝ≥0∞ m _ a)
    (hb : @Measurable Ω ℝ≥0∞ m _ b) (hAp : 0 < P A)
    (hfinite : ∀ᵐ ω ∂P, a ω ≠ 0 ∧ b ω ≠ ∞)
    (hinside : ∀ n m' : ℕ, 0 < n →
      @MeasurableSet Ω m₀ {ω | x ω < (n : ℝ≥0∞)⁻¹ ∧ (m' : ℝ≥0∞) < y ω} ∧
      ∀ᵐ ω ∂P, 0 < (P[({ω | x ω < (n : ℝ≥0∞)⁻¹ ∧ (m' : ℝ≥0∞) < y ω}).indicator
        (fun _ => (1 : ℝ)) | m]) ω) :
    0 < P {ω | ω ∈ A ∧ x ω < a ω ∧ b ω < y ω} := by
  let : MeasurableSpace Ω := m₀
  let G : Set Ω := {ω | a ω ≠ 0 ∧ b ω ≠ ∞}
  have hEq : A =ᵐ[P] A ∩ G := by
    filter_upwards [hfinite] with ω hw
    simp [G, hw]
  have hAG : 0 < P (A ∩ G) := by rwa [← measure_congr hEq]
  obtain ⟨n, k, hn, hp⟩ := exists_positive_measure_uniform_thresholds P (A ∩ G) a b hAG
    (by intro ω hω; exact hω.2)
  let F : Set Ω := {ω | ω ∈ A ∧ (n : ℝ≥0∞)⁻¹ < a ω ∧ b ω < (k : ℝ≥0∞)}
  let H : Set Ω := {ω | x ω < (n : ℝ≥0∞)⁻¹ ∧ (k : ℝ≥0∞) < y ω}
  have hFm : MeasurableSet[m] F :=
    hA.inter ((measurableSet_lt measurable_const ha).inter (measurableSet_lt hb measurable_const))
  have hFp : 0 < P F := hp.trans_le (measure_mono (by
    intro ω hω
    exact ⟨hω.1.1, hω.2.1, hω.2.2⟩))
  have hFH : 0 < P (F ∩ H) :=
    measure_inter_pos_of_condExp_indicator_pos P m hm hFm (hinside n k hn).1 hFp (hinside n k hn).2
  refine hFH.trans_le (measure_mono ?_)
  intro ω hω
  exact ⟨hω.1.1, hω.2.1.trans hω.1.2.1, hω.1.2.2.trans hω.2.2⟩

#print axioms positive_comparisons_of_conditional_thresholds
end HarmonicBalls
