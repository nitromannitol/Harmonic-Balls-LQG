import HarmonicBalls.Steps.Sec11.InternalMetricHomeomorph
import HarmonicBalls.Steps.Sec11.AnnulusGreenDilation
import HarmonicBalls.Steps.Sec11.InternalPinchScales
import HarmonicBalls.Steps.Sec11.PinchConstantScaling

/-! # Geometric dilation of the pinch metric bounds -/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- Positive dilation sends a sphere to the sphere with scaled center and radius. -/
theorem image_real_smul_sphere {k : ℝ} (hk : 0 < k) (z : ℂ) (r : ℝ) :
    (fun x : ℂ => k • x) '' sphere z r = sphere (k • z) (k * r) := by
  have hmem (x : ℂ) : k • x ∈ sphere (k • z) (k * r) ↔ x ∈ sphere z r := by
    simp only [mem_sphere, dist_smul₀, Real.norm_eq_abs, abs_of_pos hk]
    exact ⟨mul_left_cancel₀ hk.ne', congrArg (k * ·)⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).2 hx
  · intro hy
    refine ⟨k⁻¹ • y, (hmem _).1 ?_, ?_⟩
    · simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using hy
    · simp [hk.ne']

/-- Dilation commutes with scaling and translating a deterministic set. -/
theorem image_real_smul_rescaledSet (k r : ℝ) (z : ℂ) (A : Set ℂ) :
    (fun x : ℂ => k • x) '' rescaledSet A r z = rescaledSet A (k * r) (k • z) := by
  unfold rescaledSet
  rw [← image_comp]
  congr 1
  funext x
  simp only [Function.comp_apply, Complex.real_smul, Complex.ofReal_mul]
  ring

/-- Positive geometric dilation transports the strengthened pinch event. -/
theorem pinchPointEventWithInternalBounds_comp_real_smul
    (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M r : ℝ) (z : ℂ)
    {k : ℝ} (hk : 0 < k) :
    pinchPointEventWithInternalBounds (μ.map (fun x : ℂ => k⁻¹ • x))
        (fun x y => D (k • x) (k • y)) U T Q' Q M r z ↔
      pinchPointEventWithInternalBounds μ D U T Q' Q M (k * r) (k • z) := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero k hk.ne'
  have he (x : ℂ) : e x = k • x := rfl
  have hball : e '' ball z (6 * r) = ball (k • z) (6 * (k * r)) := by
    simpa only [he, mul_assoc, mul_left_comm] using image_real_smul_ball hk z (6 * r)
  have hsphere : e '' sphere z (5 * r) = sphere (k • z) (5 * (k * r)) := by
    simpa only [he, mul_assoc, mul_left_comm] using image_real_smul_sphere hk z (5 * r)
  have hres (A : Set ℂ) : e '' rescaledSet A r z = rescaledSet A (k * r) (k • z) := by
    simpa only [he] using image_real_smul_rescaledSet k r z A
  have hmap (A : Set ℂ) : (μ.map (fun x : ℂ => k⁻¹ • x)) (rescaledSet A r z) =
      μ (rescaledSet A (k * r) (k • z)) := by
    change (μ.map e.symm) (rescaledSet A r z) = _
    rw [e.symm.measurableEmbedding.map_apply, e.preimage_symm, hres]
  change pinchPointEventWithInternalBounds (μ.map (fun x : ℂ => k⁻¹ • x))
    (fun x y => D (e x) (e y)) U T Q' Q M r z ↔ _
  unfold pinchPointEventWithInternalBounds
  rw [iSup_internalMetric_comp_homeomorph, iSup_iSup_internalMetric_comp_homeomorph,
    setDist_comp_homeomorph, setDist_comp_homeomorph, e.image_frontier]
  simp only [hball, hsphere, hres, image_singleton]
  simp only [he, hmap, annulusGreenPotentialSup_comp_real_smul μ hk, mul_left_comm]

/-- Geometric dilation and independent positive normalizations transport the
strengthened pinch event to the corresponding original scale. -/
theorem pinchPointEventWithInternalBounds_normalized_dilation
    (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M r : ℝ) (z : ℂ)
    {k c : ℝ} (hk : 0 < k) (hc : 0 < c) {a : ℝ≥0∞} (ha : a ≠ 0) (hat : a ≠ ∞) :
    pinchPointEventWithInternalBounds (a • μ.map (fun x : ℂ => k⁻¹ • x))
        (fun x y => c * D (k • x) (k • y)) U T Q' Q M r z ↔
      pinchPointEventWithInternalBounds μ D U T Q' Q M (k * r) (k • z) := by
  rw [pinchPointEventWithInternalBounds_const_mul _ _ _ _ _ _ _ _ _ hc ha hat,
    pinchPointEventWithInternalBounds_comp_real_smul _ _ _ _ _ _ _ _ _ hk]

end HarmonicBalls
