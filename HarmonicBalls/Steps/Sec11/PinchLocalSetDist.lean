import HarmonicBalls.Steps.Sec11.LocalPathLength
import HarmonicBalls.Steps.Sec11.PathCrossings
import HarmonicBalls.Steps.Sec11.InternalPinchScales

/-!
# Locality of the boundary distances in a pinch event

The infimum over the entire boundary permits paths to be stopped at their
first boundary crossing. Thus these set distances are determined by the
internal metric of the larger ball.
-/

namespace HarmonicBalls

open Set Metric Topology MeasureTheory
open scoped ENNReal

/-- The `Q'`-to-`∂Q` distance in the pinch event is the corresponding
infimum of internal distances in the radius-six ball. -/
theorem ofReal_setDist_pinch_boundary_eq_internalMetric
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (setDist D (rescaledSet Q' r z) (frontier (rescaledSet Q r z))) =
      ⨅ x ∈ rescaledSet Q' r z, ⨅ y ∈ frontier (rescaledSet Q r z),
        internalMetric D (ball z (6 * r)) x y := by
  have hQopen := isOpen_rescaledSet hconfig.isOpen_Q (ne_of_gt hr) z
  have hQ'sub : rescaledSet Q' r z ⊆ rescaledSet Q r z := by
    apply Set.image_mono
    exact subset_closure.trans hconfig.closure_Q'_subset
  have hQsub : rescaledSet Q r z ⊆ ball z (5 * r) := by
    apply rescaledSet_subset_ball _ hr z
    exact hconfig.Q_subset.trans (fun _ hx => hx.1.1)
  have h5 : 0 < 5 * r := by positivity
  have hQclosure : closure (rescaledSet Q r z) ⊆ ball z (6 * r) := by
    apply (closure_mono hQsub).trans
    rw [closure_ball z h5.ne']
    intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball]
    nlinarith
  have hQ'ne : (rescaledSet Q' r z).Nonempty := hconfig.isConnected_Q'.nonempty.image _
  have hQne : (rescaledSet Q r z).Nonempty := hconfig.isConnected_Q.nonempty.image _
  have hQproper : rescaledSet Q r z ≠ univ := by
    obtain ⟨w, hw⟩ := (NormedSpace.sphere_nonempty (x := z) (r := 6 * r)).2 (by positivity)
    intro heq
    have hwQ : w ∈ rescaledSet Q r z := by rw [heq]; trivial
    have hw5 := hQsub hwQ
    rw [mem_sphere] at hw
    rw [mem_ball] at hw5
    nlinarith
  have hfront : (frontier (rescaledSet Q r z)).Nonempty :=
    nonempty_frontier_iff.mpr ⟨hQne, hQproper⟩
  exact ofReal_setDist_boundary_eq_internalMetric hD hQopen hQ'sub hQclosure hQ'ne hfront

/-- If two length metrics have the same internal metric on a neighborhood
of the closure, they have the same distance from an interior set to the
boundary. -/
theorem ofReal_setDist_boundary_eq_of_internalMetric_eq
    {D₁ D₂ : ℂ → ℂ → ℝ} (hD₁ : IsEuclideanLengthMetric D₁)
    (hD₂ : IsEuclideanLengthMetric D₂) {A U V : Set ℂ} (hU : IsOpen U)
    (hAU : A ⊆ U) (hUV : closure U ⊆ V) (hA : A.Nonempty)
    (hfront : (frontier U).Nonempty)
    (heq : ∀ x ∈ V, ∀ y ∈ V, internalMetric D₁ V x y = internalMetric D₂ V x y) :
    ENNReal.ofReal (setDist D₁ A (frontier U)) =
      ENNReal.ofReal (setDist D₂ A (frontier U)) := by
  rw [ofReal_setDist_boundary_eq_internalMetric hD₁ hU hAU hUV hA hfront,
    ofReal_setDist_boundary_eq_internalMetric hD₂ hU hAU hUV hA hfront]
  refine iInf_congr fun x => iInf_congr fun hx => iInf_congr fun y => iInf_congr fun hy => ?_
  exact heq x (hUV (subset_closure (hAU hx))) y (hUV (frontier_subset_closure hy))

/-- Agreement of the radius-six internal metrics determines the
`Q'`-to-`∂Q` distance of a pinch configuration. -/
theorem ofReal_setDist_pinch_boundary_eq_of_internalMetric_eq
    {D₁ D₂ : ℂ → ℂ → ℝ} (hD₁ : IsEuclideanLengthMetric D₁)
    (hD₂ : IsEuclideanLengthMetric D₂)
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (z : ℂ) {r : ℝ} (hr : 0 < r)
    (heq : ∀ x ∈ ball z (6 * r), ∀ y ∈ ball z (6 * r),
      internalMetric D₁ (ball z (6 * r)) x y = internalMetric D₂ (ball z (6 * r)) x y) :
    ENNReal.ofReal (setDist D₁ (rescaledSet Q' r z) (frontier (rescaledSet Q r z))) =
      ENNReal.ofReal (setDist D₂ (rescaledSet Q' r z) (frontier (rescaledSet Q r z))) := by
  have hQsub : rescaledSet Q r z ⊆ ball z (5 * r) := by
    apply rescaledSet_subset_ball _ hr z
    exact hconfig.Q_subset.trans (fun _ hx => hx.1.1)
  have h5 : 0 < 5 * r := by positivity
  have hQclosure : closure (rescaledSet Q r z) ⊆ ball z (6 * r) := by
    apply (closure_mono hQsub).trans
    rw [closure_ball z h5.ne']
    intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball]
    nlinarith
  have hQ'sub : rescaledSet Q' r z ⊆ rescaledSet Q r z :=
    Set.image_mono (subset_closure.trans hconfig.closure_Q'_subset)
  rw [ofReal_setDist_pinch_boundary_eq_internalMetric hD₁ hconfig z hr,
    ofReal_setDist_pinch_boundary_eq_internalMetric hD₂ hconfig z hr]
  refine iInf_congr fun x => iInf_congr fun hx => iInf_congr fun y => iInf_congr fun hy => ?_
  exact heq x (hQclosure (subset_closure (hQ'sub hx))) y
    (hQclosure (frontier_subset_closure hy))

/-- Agreement of the radius-six internal metrics determines the center-to-
outer-sphere distance of a pinch event. -/
theorem ofReal_setDist_center_sphere_eq_of_internalMetric_eq
    {D₁ D₂ : ℂ → ℂ → ℝ} (hD₁ : IsEuclideanLengthMetric D₁)
    (hD₂ : IsEuclideanLengthMetric D₂) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (heq : ∀ x ∈ ball z (6 * r), ∀ y ∈ ball z (6 * r),
      internalMetric D₁ (ball z (6 * r)) x y = internalMetric D₂ (ball z (6 * r)) x y) :
    ENNReal.ofReal (setDist D₁ {z} (sphere z (5 * r))) =
      ENNReal.ofReal (setDist D₂ {z} (sphere z (5 * r))) := by
  rw [ofReal_setDist_center_sphere_eq_internalMetric hD₁ z hr,
    ofReal_setDist_center_sphere_eq_internalMetric hD₂ z hr]
  refine iInf_congr fun y => iInf_congr fun hy => ?_
  apply heq z (by simp; positivity) y
  rw [mem_sphere] at hy
  rw [mem_ball]
  nlinarith

/-- With fixed measure, the strengthened pinch event depends on the metric
only through its internal metric in the radius-six ball. -/
theorem pinchPointEventWithInternalBounds_iff_of_internalMetric_eq
    {D₁ D₂ : ℂ → ℂ → ℝ} (hD₁ : IsEuclideanLengthMetric D₁)
    (hD₂ : IsEuclideanLengthMetric D₂) (μ : Measure ℂ)
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (heq : ∀ x ∈ ball z (6 * r), ∀ y ∈ ball z (6 * r),
      internalMetric D₁ (ball z (6 * r)) x y = internalMetric D₂ (ball z (6 * r)) x y) :
    pinchPointEventWithInternalBounds μ D₁ U T Q' Q M r z ↔
      pinchPointEventWithInternalBounds μ D₂ U T Q' Q M r z := by
  have hz : z ∈ ball z (6 * r) := by simp; positivity
  have hsphere : sphere z (5 * r) ⊆ ball z (6 * r) := by
    intro x hx
    rw [mem_sphere] at hx
    rw [mem_ball]
    nlinarith
  have hT : rescaledSet T r z ⊆ ball z (6 * r) := by
    have hT5 : rescaledSet T r z ⊆ ball z (5 * r) := by
      apply rescaledSet_subset_ball _ hr z
      exact hconfig.T_subset.trans (fun _ hx => hx.1)
    intro x hx
    have h := hT5 hx
    rw [mem_ball] at h ⊢
    nlinarith
  have hsup₁ : (⨆ x ∈ sphere z (5 * r), internalMetric D₁ (ball z (6 * r)) z x) =
      ⨆ x ∈ sphere z (5 * r), internalMetric D₂ (ball z (6 * r)) z x := by
    refine iSup_congr fun x => iSup_congr fun hx => ?_
    exact heq z hz x (hsphere hx)
  have hsup₂ : (⨆ x ∈ rescaledSet T r z, ⨆ y ∈ rescaledSet T r z,
      internalMetric D₁ (ball z (6 * r)) x y) =
      ⨆ x ∈ rescaledSet T r z, ⨆ y ∈ rescaledSet T r z,
      internalMetric D₂ (ball z (6 * r)) x y := by
    refine iSup_congr fun x => iSup_congr fun hx => iSup_congr fun y => iSup_congr fun hy => ?_
    exact heq x (hT hx) y (hT hy)
  have hdist₁ := ofReal_setDist_pinch_boundary_eq_of_internalMetric_eq hD₁ hD₂ hconfig z hr heq
  have hdist₂ := ofReal_setDist_center_sphere_eq_of_internalMetric_eq hD₁ hD₂ z hr heq
  simp only [pinchPointEventWithInternalBounds, hsup₁, hsup₂, hdist₁, hdist₂]

end HarmonicBalls
