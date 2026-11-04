import HarmonicBalls.Steps.Sec11.PinchLocalSetDist

/-!
# Local data for the strengthened pinch event

The annular Green potential and the mass term depend only on the measure
restricted to the same ball as the internal metric.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory
open scoped ENNReal

/-- Annular Green-potential suprema agree when the measures agree on the
annulus. -/
theorem annulusGreenPotentialSup_eq_of_restrict_eq
    {μ ν : Measure ℂ} (z : ℂ) (a b : ℝ)
    (h : μ.restrict (annulus z a b) = ν.restrict (annulus z a b)) :
    annulusGreenPotentialSup μ z a b = annulusGreenPotentialSup ν z a b := by
  unfold annulusGreenPotentialSup
  rw [h]

/-- The strengthened pinch event depends only on the measure restricted to
the radius-six ball and on the internal metric of that ball. -/
theorem pinchPointEventWithInternalBounds_iff_of_local_data
    {D₁ D₂ : ℂ → ℂ → ℝ} (hD₁ : IsEuclideanLengthMetric D₁)
    (hD₂ : IsEuclideanLengthMetric D₂) {μ₁ μ₂ : Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hmetric : ∀ x ∈ ball z (6 * r), ∀ y ∈ ball z (6 * r),
      internalMetric D₁ (ball z (6 * r)) x y = internalMetric D₂ (ball z (6 * r)) x y)
    (hmeasure : μ₁.restrict (ball z (6 * r)) = μ₂.restrict (ball z (6 * r))) :
    pinchPointEventWithInternalBounds μ₁ D₁ U T Q' Q M r z ↔
      pinchPointEventWithInternalBounds μ₂ D₂ U T Q' Q M r z := by
  have hAnn : annulus z (3 * r) (6 * r) ⊆ ball z (6 * r) := fun _ hx => hx.1
  have hAnnEq : μ₁.restrict (annulus z (3 * r) (6 * r)) =
      μ₂.restrict (annulus z (3 * r) (6 * r)) := by
    rw [← Measure.restrict_restrict_of_subset hAnn, hmeasure,
      Measure.restrict_restrict_of_subset hAnn]
  have hgreen := annulusGreenPotentialSup_eq_of_restrict_eq z (3 * r) (6 * r) hAnnEq
  have hU5 : rescaledSet U r z ⊆ ball z (5 * r) := by
    apply rescaledSet_subset_ball _ hr z
    intro x hx
    have h := hconfig.U_subset hx
    change dist x 0 < 5
    change dist x 0 < 2 ∧ _ at h
    linarith [h.1]
  have hU6 : rescaledSet U r z ⊆ ball z (6 * r) := by
    intro x hx
    have h := hU5 hx
    rw [mem_ball] at h ⊢
    nlinarith
  have hUmeas : MeasurableSet (rescaledSet U r z) :=
    (isOpen_rescaledSet hconfig.isOpen_U (ne_of_gt hr) z).measurableSet
  have hmass : μ₁ (rescaledSet U r z) = μ₂ (rescaledSet U r z) := by
    have h := congrArg (fun m : Measure ℂ => m (rescaledSet U r z)) hmeasure
    simpa only [Measure.restrict_apply hUmeas, Set.inter_eq_self_of_subset_left hU6] using h
  calc
    pinchPointEventWithInternalBounds μ₁ D₁ U T Q' Q M r z ↔
        pinchPointEventWithInternalBounds μ₁ D₂ U T Q' Q M r z :=
      pinchPointEventWithInternalBounds_iff_of_internalMetric_eq hD₁ hD₂ μ₁ hconfig M z hr hmetric
    _ ↔ pinchPointEventWithInternalBounds μ₂ D₂ U T Q' Q M r z := by
      simp only [pinchPointEventWithInternalBounds, hgreen, hmass]

end HarmonicBalls
