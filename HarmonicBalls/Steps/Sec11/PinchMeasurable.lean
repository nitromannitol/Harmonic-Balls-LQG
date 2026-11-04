import HarmonicBalls.Steps.Sec11.InternalMetricMeasurable
import HarmonicBalls.Steps.Sec11.PinchLocalSetDist
import Mathlib.MeasureTheory.Measure.NullMeasurable

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

/-- The intersection of the pinch event with a measurable set on which the
random metric is a length metric is measurable. -/
theorem measurableSet_inter_pinchPointEventWithInternalBounds
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r) {G : Set Ω} (hG : MeasurableSet G)
    (hD : ∀ ω ∈ G, IsEuclideanLengthMetric (D ω))
    (hnonneg : ∀ ω ∈ G, ∀ x y, 0 ≤ D ω x y)
    (hdist : ∀ x ∈ ball z (6 * r), ∀ y ∈ ball z (6 * r),
      Measurable fun ω => internalMetric (D ω) (ball z (6 * r)) x y)
    (hgreen : Measurable fun ω => annulusGreenPotentialSup (μ ω) z (3 * r) (6 * r))
    (hmass : Measurable fun ω => μ ω (rescaledSet U r z)) :
    MeasurableSet (G ∩ {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z}) := by
  classical
  let D' : Ω → ℂ → ℂ → ℝ := fun ω => if ω ∈ G then D ω else dist
  have hD' (ω : Ω) : IsEuclideanLengthMetric (D' ω) := by
    by_cases hω : ω ∈ G
    · simpa only [D', ite_eq_left hω] using hD ω hω
    · simpa only [D', ite_eq_right hω] using isEuclideanLengthMetric_dist
  have hnonneg' (ω : Ω) (x y : ℂ) : 0 ≤ D' ω x y := by
    by_cases hω : ω ∈ G
    · simpa only [D', ite_eq_left hω] using hnonneg ω hω x y
    · simpa only [D', ite_eq_right hω] using dist_nonneg
  have hdist' (x : ℂ) (hx : x ∈ ball z (6 * r))
      (y : ℂ) (hy : y ∈ ball z (6 * r)) :
      Measurable fun ω => internalMetric (D' ω) (ball z (6 * r)) x y := by
    have hfun : (fun ω => internalMetric (D' ω) (ball z (6 * r)) x y) =
        fun ω => if ω ∈ G then internalMetric (D ω) (ball z (6 * r)) x y else
          internalMetric dist (ball z (6 * r)) x y := by
      funext ω
      by_cases hω : ω ∈ G <;> simp only [D', hω, ite_true, ite_false]
    rw [hfun]
    exact Measurable.ite hG (hdist x hx y hy) measurable_const
  have hEvent := measurableSet_pinchPointEventWithInternalBounds hconfig M z hr
    hD' hnonneg' hdist' hgreen hmass
  have heq : G ∩ {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z} =
      G ∩ {ω | pinchPointEventWithInternalBounds (μ ω) (D' ω) U T Q' Q M r z} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor <;> rintro ⟨hω, he⟩ <;> refine ⟨hω, ?_⟩
    · simpa only [D', ite_eq_left hω] using he
    · simpa only [D', ite_eq_left hω] using he
  rw [heq]
  exact hG.inter hEvent

/-- If the measurable set of length-metric realizations has full measure,
the strengthened pinch event is null-measurable. -/
theorem nullMeasurableSet_pinchPointEventWithInternalBounds
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r) {G : Set Ω} (hG : MeasurableSet G)
    (hGae : ∀ᵐ ω ∂P, ω ∈ G)
    (hD : ∀ ω ∈ G, IsEuclideanLengthMetric (D ω))
    (hnonneg : ∀ ω ∈ G, ∀ x y, 0 ≤ D ω x y)
    (hdist : ∀ x ∈ ball z (6 * r), ∀ y ∈ ball z (6 * r),
      Measurable fun ω => internalMetric (D ω) (ball z (6 * r)) x y)
    (hgreen : Measurable fun ω => annulusGreenPotentialSup (μ ω) z (3 * r) (6 * r))
    (hmass : Measurable fun ω => μ ω (rescaledSet U r z)) :
    NullMeasurableSet {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z} P := by
  have hmeas := measurableSet_inter_pinchPointEventWithInternalBounds
    hconfig M z hr hG hD hnonneg hdist hgreen hmass
  apply hmeas.nullMeasurableSet.congr
  filter_upwards [hGae] with ω hω
  simp only [mem_inter_iff, mem_ofPred_eq, hω, true_and]

/-- Almost-sure length-metric regularity suffices for null measurability;
the full-measure set need not be given in advance. -/
theorem nullMeasurableSet_pinchPointEventWithInternalBounds_of_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hdist : ∀ x ∈ ball z (6 * r), ∀ y ∈ ball z (6 * r),
      Measurable fun ω => internalMetric (D ω) (ball z (6 * r)) x y)
    (hgreen : Measurable fun ω => annulusGreenPotentialSup (μ ω) z (3 * r) (6 * r))
    (hmass : Measurable fun ω => μ ω (rescaledSet U r z)) :
    NullMeasurableSet {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z} P := by
  let H : Set Ω := {ω | IsEuclideanLengthMetric (D ω)}
  have hH : NullMeasurableSet H P := by
    apply (nullMeasurableSet_univ (μ := P)).congr
    filter_upwards [hD] with ω hω
    simp only [mem_univ, H, mem_ofPred_eq, hω]
  obtain ⟨G, hsub, hG, hGeq⟩ := hH.exists_measurable_subset_ae_eq
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [hGeq, hD] with ω heq hω
    exact Eq.mpr heq hω
  apply nullMeasurableSet_pinchPointEventWithInternalBounds hconfig M z hr hG hGae
    (fun ω hω => hsub hω) ?_ hdist hgreen hmass
  intro ω hω x y
  have hm : IsEuclideanLengthMetric (D ω) := hsub hω
  have htri := hm.triangle x y x
  rw [hm.self_eq_zero, hm.symm y x] at htri
  linarith

end HarmonicBalls
