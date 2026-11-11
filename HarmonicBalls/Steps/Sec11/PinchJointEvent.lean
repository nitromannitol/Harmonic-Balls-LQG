import HarmonicBalls.Steps.Sec11.InternalMetricPullback
import HarmonicBalls.Steps.Sec11.PinchJointMeasure
import HarmonicBalls.Steps.Sec11.PinchMetricDilation
import HarmonicBalls.Steps.Sec11.PinchMeasurable

/-! # Joint measurability of pinch events -/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

/-- Recentering the measure and the metric transports the strengthened
pinch event to the origin. -/
theorem pinchPointEventWithInternalBounds_translate
    (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M r : ℝ) (z : ℂ) :
    pinchPointEventWithInternalBounds (μ.map (fun y : ℂ => y - z))
        (fun x y => D (x + z) (y + z)) U T Q' Q M r 0 ↔
      pinchPointEventWithInternalBounds μ D U T Q' Q M r z := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.addRight z
  have he (x : ℂ) : e x = x + z := rfl
  have hball (a : ℝ) : e '' ball 0 a = ball z a := by
    rw [← e.preimage_symm]
    ext x
    simp only [mem_preimage, mem_ball, dist_eq_norm, sub_zero]
    rfl
  have hsphere (a : ℝ) : e '' sphere 0 a = sphere z a := by
    rw [← e.preimage_symm]
    ext x
    simp only [mem_preimage, mem_sphere, dist_eq_norm, sub_zero]
    rfl
  have hres (A : Set ℂ) : e '' rescaledSet A r 0 = rescaledSet A r z := by
    unfold rescaledSet
    rw [← image_comp]
    congr 1
    funext x
    simp only [Function.comp_apply, he, add_zero]
  have hmap (A : Set ℂ) : (μ.map (fun y : ℂ => y - z)) (rescaledSet A r 0) =
      μ (rescaledSet A r z) := by
    change (μ.map e.symm) (rescaledSet A r 0) = _
    rw [e.symm.measurableEmbedding.map_apply, e.preimage_symm, hres]
  change pinchPointEventWithInternalBounds (μ.map (fun y : ℂ => y - z))
    (fun x y => D (e x) (e y)) U T Q' Q M r 0 ↔ _
  unfold pinchPointEventWithInternalBounds
  rw [iSup_internalMetric_comp_homeomorph, iSup_iSup_internalMetric_comp_homeomorph,
    setDist_comp_homeomorph, setDist_comp_homeomorph, e.image_frontier]
  simp only [hball, hsphere, hres, image_singleton]
  simp only [he, zero_add, hmap, annulusGreenPotentialSup_map_sub]

/-- The strengthened pinch event is jointly measurable in the sample and
center when the random measure is represented by an s-finite kernel. -/
theorem measurableSet_kernel_pinchPointEventWithInternalBounds
    {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
    {D : Ω → ℂ → ℂ → ℝ} {U T Q' Q : Set ℂ}
    (hconfig : IsPinchPointConfiguration U T Q' Q) (M : ℝ) {r : ℝ} (hr : 0 < r)
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ ω, IsEuclideanLengthMetric (D ω)) :
    MeasurableSet {p : Ω × ℂ |
      pinchPointEventWithInternalBounds (κ p.1) (D p.1) U T Q' Q M r p.2} := by
  let D' : (Ω × ℂ) → ℂ → ℂ → ℝ := fun p x y => D p.1 (x + p.2) (y + p.2)
  let μ' : (Ω × ℂ) → Measure ℂ := fun p => (κ p.1).map (fun y : ℂ => y - p.2)
  have hD' : ∀ x y, Measurable fun p => D' p x y :=
    fun x y => measurable_euclideanLengthMetric_translate hD hmetric x y
  have hmetric' : ∀ p, IsEuclideanLengthMetric (D' p) :=
    fun p => (hmetric p.1).comp_homeomorph (Homeomorph.addRight p.2)
  have hnonneg : ∀ p x y, 0 ≤ D' p x y := by
    intro p x y
    have h := (hmetric' p).triangle x y x
    rw [(hmetric' p).self_eq_zero, (hmetric' p).symm y x] at h
    linarith
  have hdist : ∀ x ∈ ball (0 : ℂ) (6 * r), ∀ y ∈ ball (0 : ℂ) (6 * r),
      Measurable fun p => internalMetric (D' p) (ball 0 (6 * r)) x y := by
    intro x hx y hy
    exact measurable_internalMetric_of_lengthMetric isOpen_ball hx y hD' hmetric'
  have hμ' : Measurable μ' := measurable_kernel_map_sub κ
  have hgreen : Measurable fun p => annulusGreenPotentialSup (μ' p) 0 (3 * r) (6 * r) :=
    (measurable_annulusGreenPotentialSup 0 (3 * r) (6 * r)).comp hμ'
  have hmass : Measurable fun p => μ' p (rescaledSet U r 0) :=
    (Measure.measurable_coe (isOpen_rescaledSet hconfig.isOpen_U hr.ne' 0).measurableSet).comp hμ'
  have hm := measurableSet_pinchPointEventWithInternalBounds hconfig M 0 hr hmetric'
    hnonneg hdist hgreen hmass
  convert hm using 1
  ext p
  exact (pinchPointEventWithInternalBounds_translate (κ p.1) (D p.1) U T Q' Q M r p.2).symm


end HarmonicBalls
