import HarmonicBalls.Steps.Sec11.InternalMetricMeasurable
import HarmonicBalls.Steps.Sec11.PinchLocalSetDist

/-! # Measurability of the strengthened pinch event -/

namespace HarmonicBalls

open Set Metric MeasureTheory Topology
open scoped ENNReal

/-- The strengthened pinch event is measurable if the internal distances at
fixed points, the annular potential, and the relevant mass are measurable. -/
theorem measurableSet_pinchPointEventWithInternalBounds
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hD : ∀ ω, IsEuclideanLengthMetric (D ω))
    (hnonneg : ∀ ω x y, 0 ≤ D ω x y)
    (hdist : ∀ x ∈ ball z (6 * r), ∀ y ∈ ball z (6 * r),
      Measurable fun ω => internalMetric (D ω) (ball z (6 * r)) x y)
    (hgreen : Measurable fun ω => annulusGreenPotentialSup (μ ω) z (3 * r) (6 * r))
    (hmass : Measurable fun ω => μ ω (rescaledSet U r z)) :
    MeasurableSet {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z} := by
  let V := ball z (6 * r)
  let S := sphere z (5 * r)
  let A := rescaledSet Q' r z
  let B := frontier (rescaledSet Q r z)
  let C := rescaledSet T r z
  have hz : ({z} : Set ℂ) ⊆ V := by
    intro x hx
    have hxz : x = z := mem_singleton_iff.mp hx
    subst x
    change z ∈ ball z (6 * r)
    simp only [mem_ball, dist_self]
    positivity
  have hs : S ⊆ V := by
    intro x hx
    change x ∈ sphere z (5 * r) at hx
    change x ∈ ball z (6 * r)
    rw [mem_sphere] at hx
    rw [mem_ball]
    nlinarith
  have hc : C ⊆ V := by
    have hC5 : rescaledSet T r z ⊆ ball z (5 * r) := by
      apply rescaledSet_subset_ball _ hr z
      exact hconfig.T_subset.trans (fun _ hx => hx.1)
    intro x hx
    have hx5 := hC5 hx
    change x ∈ ball z (6 * r)
    rw [mem_ball] at hx5 ⊢
    nlinarith
  have hQ : rescaledSet Q r z ⊆ ball z (5 * r) := by
    apply rescaledSet_subset_ball _ hr z
    exact hconfig.Q_subset.trans (fun _ hx => hx.1.1)
  have hQclosure : closure (rescaledSet Q r z) ⊆ V := by
    apply (closure_mono hQ).trans
    have h5 : 0 < 5 * r := by positivity
    rw [closure_ball z h5.ne']
    intro x hx
    rw [mem_closedBall] at hx
    change x ∈ ball z (6 * r)
    rw [mem_ball]
    nlinarith
  have ha : A ⊆ V := by
    apply (Set.image_mono (subset_closure.trans hconfig.closure_Q'_subset)).trans
    exact subset_closure.trans hQclosure
  have hb : B ⊆ V := frontier_subset_closure.trans hQclosure
  have hsupS := measurable_iSup_internalMetric (V := V) (A := {z}) (B := S)
    isOpen_ball hz hs hD hnonneg (fun x hx y hy => hdist x (hz hx) y (hs hy))
  have hsupC := measurable_iSup_internalMetric (V := V) (A := C) (B := C)
    isOpen_ball hc hc hD hnonneg (fun x hx y hy => hdist x (hc hx) y (hc hy))
  have hinfQ := measurable_iInf_internalMetric (V := V) (A := A) (B := B)
    isOpen_ball ha hb hD hnonneg (fun x hx y hy => hdist x (ha hx) y (hb hy))
  have hinfS := measurable_iInf_internalMetric (V := V) (A := {z}) (B := S)
    isOpen_ball hz hs hD hnonneg (fun x hx y hy => hdist x (hz hx) y (hs hy))
  have hfirst := measurableSet_lt hsupS hinfQ
  have hsecond := measurableSet_lt hsupC hinfS
  have hthird := measurableSet_lt
    ((measurable_const : Measurable (fun _ : Ω => ENNReal.ofReal M)).mul hgreen) hmass
  convert hfirst.inter (hsecond.inter hthird) using 1
  ext ω
  simp only [pinchPointEventWithInternalBounds, mem_ofPred_eq, mem_inter_iff,
    iSup_singleton, iInf_singleton] at *
  rw [ofReal_setDist_pinch_boundary_eq_internalMetric (hD ω) hconfig z hr,
    ofReal_setDist_center_sphere_eq_internalMetric (hD ω) z hr]
  rfl

end HarmonicBalls
