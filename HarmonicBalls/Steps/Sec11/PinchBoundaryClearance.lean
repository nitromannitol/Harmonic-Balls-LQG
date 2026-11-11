import HarmonicBalls.Steps.Sec11.InternalPinchScales
import HarmonicBalls.Steps.Sec11.BoundaryClearance

/-! # Boundary clearance for the strengthened pinch event

The global pinch inequalities imply their internal counterparts whenever the
relevant pairs have enough distance from the complement of the local ball.
This identifies a geometric condition still needed for a positivity argument.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- The pairs used in the pinch inequalities have boundary clearance in the
ball where the internal metric is taken. -/
def PinchBoundaryClearance (D : ℂ → ℂ → ℝ) (T : Set ℂ) (r : ℝ) (z : ℂ) : Prop :=
  (∀ x ∈ sphere z (5 * r), ∃ δ : ℝ,
    (∀ w ∉ ball z (6 * r), δ ≤ D z w) ∧ D z x < δ) ∧
  (∀ x ∈ rescaledSet T r z, ∀ y ∈ rescaledSet T r z, ∃ δ : ℝ,
    (∀ w ∉ ball z (6 * r), δ ≤ D x w) ∧ D x y < δ)

/-- Boundary clearance upgrades the global pinch event to the strengthened
internal-metric event. -/
theorem pinchPointEventWithInternalBounds_of_boundaryClearance
    {μ : Measure ℂ} {D : ℂ → ℂ → ℝ} {U T Q' Q : Set ℂ} {M r : ℝ} {z : ℂ}
    (hD : IsEuclideanLengthMetric D) (hnonneg : ∀ x y, 0 ≤ D x y)
    (hc : PinchBoundaryClearance D T r z)
    (hp : pinchPointEvent μ D U T Q' Q M r z) :
    pinchPointEventWithInternalBounds μ D U T Q' Q M r z := by
  have hfirst : (⨆ x ∈ sphere z (5 * r), internalMetric D (ball z (6 * r)) z x) =
      ⨆ x ∈ sphere z (5 * r), ENNReal.ofReal (D z x) := by
    apply iSup_congr
    intro x
    apply iSup_congr
    intro hx
    obtain ⟨δ, hδ, hxδ⟩ := hc.1 x hx
    exact hD.internalMetric_eq_of_boundary_clearance hnonneg hδ hxδ
  have hsecond : (⨆ x ∈ rescaledSet T r z, ⨆ y ∈ rescaledSet T r z,
      internalMetric D (ball z (6 * r)) x y) =
      ⨆ x ∈ rescaledSet T r z, ⨆ y ∈ rescaledSet T r z, ENNReal.ofReal (D x y) := by
    apply iSup_congr
    intro x
    apply iSup_congr
    intro hx
    apply iSup_congr
    intro y
    apply iSup_congr
    intro hy
    obtain ⟨δ, hδ, hxy⟩ := hc.2 x hx y hy
    exact hD.internalMetric_eq_of_boundary_clearance hnonneg hδ hxy
  exact ⟨hfirst ▸ hp.1, hsecond ▸ hp.2.1, hp.2.2⟩

/-- Positive mass of global pinch events satisfying boundary clearance implies
positive mass of the strengthened event. -/
theorem measure_pos_pinchPointEventWithInternalBounds_of_boundaryClearance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M r : ℝ) (z : ℂ)
    (hpos : 0 < P {ω | IsEuclideanLengthMetric (D ω) ∧ (∀ x y, 0 ≤ D ω x y) ∧
      PinchBoundaryClearance (D ω) T r z ∧ pinchPointEvent (μ ω) (D ω) U T Q' Q M r z}) :
    0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z} := by
  apply lt_of_lt_of_le hpos
  apply measure_mono
  intro ω hω
  exact pinchPointEventWithInternalBounds_of_boundaryClearance hω.1 hω.2.1 hω.2.2.1 hω.2.2.2


end HarmonicBalls
