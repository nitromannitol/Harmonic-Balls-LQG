import HarmonicBalls.Proofs.Sec6.NearbyAnnulusCollar
import HarmonicBalls.Proofs.Sec6.BrownianAvoidance

/-! # Avoidance comparison through a boundary collar

After exiting the displaced domain, a path must return to the inner core
before it can invalidate the extended-witness avoidance event. The return
probability is independent of the witness set.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set MarkovProcess
open scoped ENNReal NNReal

/-- If a path stays in `Y` until leaving `B`, then failure of the avoidance
event in `A` with the collar-extended witness forces a return to `C` after
leaving `B` and before leaving `A`. No regularity of the sets is required. -/
theorem stay_subset_collar_avoidance_or_return
    (A B C Y : Set ℂ) :
    {ω : ContinuousPath ℂ | ContinuousPath.exitTime B ω ≤ ContinuousPath.exitTime Y ω} ⊆
      {ω | ContinuousPath.exitTime A ω ≤
        ContinuousPath.exitTime ((A ∩ Y) ∪ (A \ C)) ω} ∪
      {ω | ∃ t : ℝ≥0, ContinuousPath.exitTime B ω ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < ContinuousPath.exitTime A ω ∧ ω t ∈ C} := by
  intro ω hω
  by_cases hreturn : ∃ t : ℝ≥0, ContinuousPath.exitTime B ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime A ω ∧ ω t ∈ C
  · exact Or.inr hreturn
  · left
    change ContinuousPath.exitTime A ω ≤ ContinuousPath.exitTime ((A ∩ Y) ∪ (A \ C)) ω
    rw [ContinuousPath.le_exitTime_iff]
    intro t ht
    by_contra hle
    have htA : (t : ℝ≥0∞) < ContinuousPath.exitTime A ω := lt_of_not_ge hle
    have hxA := ContinuousPath.mem_of_lt_exitTime A ω t htA
    have hxC : ω t ∈ C := by
      by_contra hxC
      exact ht (Or.inr ⟨hxA, hxC⟩)
    have hxY : ω t ∉ Y := by
      intro hxY
      exact ht (Or.inl ⟨hxA, hxY⟩)
    have htB := hω.trans (ContinuousPath.exitTime_le_of_notMem Y ω t hxY)
    exact hreturn ⟨t, htB, htA, hxC⟩

/-- The avoidance probability is bounded by that for the extended witness
plus the probability of returning to the core. The estimate uses outer measure
and applies to arbitrary sets. -/
theorem stay_probability_le_collar_avoidance_add_return
    (ν : Measure (ContinuousPath ℂ)) (A B C Y : Set ℂ) :
    ν {ω | ContinuousPath.exitTime B ω ≤ ContinuousPath.exitTime Y ω} ≤
      ν {ω | ContinuousPath.exitTime A ω ≤
        ContinuousPath.exitTime ((A ∩ Y) ∪ (A \ C)) ω} +
      ν {ω | ∃ t : ℝ≥0, ContinuousPath.exitTime B ω ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < ContinuousPath.exitTime A ω ∧ ω t ∈ C} := by
  exact (measure_mono (stay_subset_collar_avoidance_or_return A B C Y)).trans
    (measure_union_le _ _)

end HarmonicBalls.Section6
