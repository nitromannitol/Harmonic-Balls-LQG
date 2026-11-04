import HarmonicBalls.Steps.Sec11.InternalMetricHomeomorph
import HarmonicBalls.Steps.Sec11.PinchJointMetric
import HarmonicBalls.Steps.Sec11.CountableClearanceChains

/-! # Pullbacks of Euclidean length metrics -/

namespace HarmonicBalls

open Set MeasureTheory Metric
open scoped ENNReal

/-- Pullback by a homeomorphism preserves the property of being a Euclidean
length metric. -/
theorem IsEuclideanLengthMetric.comp_homeomorph {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) (e : ℂ ≃ₜ ℂ) :
    IsEuclideanLengthMetric (fun x y => D (e x) (e y)) := by
  refine ⟨fun x => hD.self_eq_zero _, ?_, fun x y => hD.symm _ _,
    fun x y z => hD.triangle _ _ _, ?_, ?_⟩
  · intro x y h
    exact e.injective (hD.eq_of_eq_zero _ _ h)
  · intro U
    constructor
    · intro hU x hx
      have himage : IsOpen (e '' U) := e.isOpenMap _ hU
      obtain ⟨ε, hε, hball⟩ := (hD.isOpen_iff (e '' U)).mp himage (e x) ⟨x, hx, rfl⟩
      refine ⟨ε, hε, fun y hy => ?_⟩
      obtain ⟨v, hv, heq⟩ := hball (e y) hy
      exact e.injective heq ▸ hv
    · intro hU
      have himage : IsOpen (e '' U) := (hD.isOpen_iff (e '' U)).mpr (by
        intro x hx
        obtain ⟨v, hv, rfl⟩ := hx
        obtain ⟨ε, hε, hb⟩ := hU v hv
        refine ⟨ε, hε, fun y hy => ?_⟩
        exact ⟨e.symm y, hb _ (by simpa only [e.apply_symm_apply] using hy), e.apply_symm_apply y⟩)
      have hpre : e ⁻¹' (e '' U) = U := e.injective.preimage_image U
      rw [← hpre]
      exact himage.preimage e.continuous
  · intro x y
    rw [internalMetric_comp_homeomorph]
    simpa only [Set.image_univ, e.surjective.range_eq] using hD.ofReal_eq_internalMetric (e x) (e y)

/-- The internal metric in a translated open domain is jointly measurable
in the realization and the translating center. -/
theorem measurable_internalMetric_translate
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ}
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ ω, IsEuclideanLengthMetric (D ω))
    {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U) (y : ℂ) :
    Measurable fun p : Ω × ℂ =>
      internalMetric (D p.1) ((Homeomorph.addRight p.2) '' U) (x + p.2) (y + p.2) := by
  let D' : (Ω × ℂ) → ℂ → ℂ → ℝ := fun p x y => D p.1 (x + p.2) (y + p.2)
  have hD' : ∀ x y, Measurable fun p => D' p x y :=
    fun x y => measurable_euclideanLengthMetric_translate hD hmetric x y
  have hmetric' : ∀ p, IsEuclideanLengthMetric (D' p) :=
    fun p => (hmetric p.1).comp_homeomorph (Homeomorph.addRight p.2)
  have hm := measurable_internalMetric_of_lengthMetric hU hx y hD' hmetric'
  convert hm using 1
  ext p
  exact (internalMetric_comp_homeomorph (D p.1) (Homeomorph.addRight p.2) U x y).symm

#print axioms IsEuclideanLengthMetric.comp_homeomorph
#print axioms measurable_internalMetric_translate

end HarmonicBalls
