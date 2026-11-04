import HarmonicBalls.Steps.Sec11.PinchBoundaryClearance

/-! # A quantitative reduction for pinch-event positivity

A strict upper bound for the mass of global pinch events without clearance
suffices for positivity of the strengthened event. No such estimate is assumed
or proved here for the LQG metric.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- A strict bound on the part of an event outside another event forces a
positive intersection. Measurability of either event is not needed. -/
theorem measure_inter_pos_of_measure_diff_lt
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A B : Set Ω)
    (h : P (A \ B) < P A) : 0 < P (A ∩ B) := by
  classical
  by_contra hn
  have hz : P (A ∩ B) = 0 := le_antisymm (not_lt.mp hn) zero_le
  have hu : A = (A ∩ B) ∪ (A \ B) := by
    ext ω
    simp only [mem_union, mem_inter_iff, mem_sdiff]
    tauto
  have hb : P A ≤ P (A ∩ B) + P (A \ B) := by
    calc
      P A = P ((A ∩ B) ∪ (A \ B)) := congrArg P hu
      _ ≤ P (A ∩ B) + P (A \ B) := measure_union_le _ _
  rw [hz, zero_add] at hb
  exact (not_le_of_gt h) hb

/-- If global pinch events lacking boundary clearance have smaller mass than
all global pinch events with a length metric, the strengthened event has
positive mass. -/
theorem measure_pos_internal_pinch_of_clearance_failure_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (U T Q' Q : Set ℂ) (M r : ℝ) (z : ℂ)
    (hbound : P ({ω | IsEuclideanLengthMetric (D ω) ∧ (∀ x y, 0 ≤ D ω x y) ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Q M r z} \
      {ω | PinchBoundaryClearance (D ω) T r z}) <
      P {ω | IsEuclideanLengthMetric (D ω) ∧ (∀ x y, 0 ≤ D ω x y) ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Q M r z}) :
    0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z} := by
  let A : Set Ω := {ω | IsEuclideanLengthMetric (D ω) ∧ (∀ x y, 0 ≤ D ω x y) ∧
    pinchPointEvent (μ ω) (D ω) U T Q' Q M r z}
  let B : Set Ω := {ω | PinchBoundaryClearance (D ω) T r z}
  have hpos : 0 < P (A ∩ B) := measure_inter_pos_of_measure_diff_lt P A B hbound
  apply lt_of_lt_of_le hpos
  apply measure_mono
  intro ω hω
  exact pinchPointEventWithInternalBounds_of_boundaryClearance
    hω.1.1 hω.1.2.1 hω.2 hω.1.2.2

/-- The quantitative clearance estimate supplies an admissible positive rate
for any finite-probability application of the frequency criterion. -/
theorem exists_positive_pinch_rate_of_clearance_failure_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (U T Q' Q : Set ℂ) (M r : ℝ) (z : ℂ)
    (hbound : P ({ω | IsEuclideanLengthMetric (D ω) ∧ (∀ x y, 0 ≤ D ω x y) ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Q M r z} \
      {ω | PinchBoundaryClearance (D ω) T r z}) <
      P {ω | IsEuclideanLengthMetric (D ω) ∧ (∀ x y, 0 ≤ D ω x y) ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Q M r z}) :
    ∃ δ : ℝ, 0 < δ ∧ δ < (P {ω |
      pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z}).toReal := by
  have hp := measure_pos_internal_pinch_of_clearance_failure_bound P μ D U T Q' Q M r z hbound
  have hreal : 0 < (P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' Q M r z}).toReal := ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top P _)
  exact ⟨_, half_pos hreal, half_lt_self hreal⟩

#print axioms measure_inter_pos_of_measure_diff_lt
#print axioms measure_pos_internal_pinch_of_clearance_failure_bound
#print axioms exists_positive_pinch_rate_of_clearance_failure_bound

end HarmonicBalls
