import HarmonicBalls.Steps.Sec11.PinchLocalEvent
import HarmonicBalls.Steps.Sec11.PinchConstantScaling

/-! # Local pinch events from normalized metric and measure data -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter
open scoped ENNReal

/-- Positive multiplication preserves the Euclidean length-metric property. -/
theorem IsEuclideanLengthMetric.const_mul {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {c : ℝ} (hc : 0 < c) :
    IsEuclideanLengthMetric (fun x y => c * D x y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; simp [hD.self_eq_zero]
  · intro x y hxy
    apply hD.eq_of_eq_zero x y
    exact (mul_eq_zero.mp hxy).resolve_left hc.ne'
  · intro x y; rw [hD.symm x y]
  · intro x y z
    simpa only [mul_add] using mul_le_mul_of_nonneg_left (hD.triangle x y z) hc.le
  · intro U
    rw [hD.isOpen_iff]
    constructor
    · intro h x hx
      obtain ⟨ε, hε, hεU⟩ := h x hx
      refine ⟨c * ε, mul_pos hc hε, ?_⟩
      intro y hy
      apply hεU y
      nlinarith
    · intro h x hx
      obtain ⟨ε, hε, hεU⟩ := h x hx
      refine ⟨ε / c, div_pos hε hc, ?_⟩
      intro y hy
      apply hεU y
      simpa only [mul_comm] using (lt_div_iff₀ hc).mp hy
  · intro x y
    rw [ENNReal.ofReal_mul hc.le, hD.ofReal_eq_internalMetric,
      internalMetric_const_mul D hc]

/-- If normalized metric and measure data are locally measurable, the pinch
event has a local representative. The random normalizing factors need not be
measurable, because they cancel from the event itself. -/
theorem exists_local_pinchEvent_representative_of_normalized_data
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {m : MeasurableSpace Ω}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ} {G : Ω → ℂ → ℂ → ℝ≥0∞}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (c : Ω → ℝ) (a : Ω → ℝ≥0∞)
    (hscale : ∀ᵐ ω ∂P, 0 < c ω ∧ a ω ≠ 0 ∧ a ω ≠ ∞)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hG : ∀ x y, Measurable[m] fun ω => G ω x y)
    (hGeq : ∀ᵐ ω ∂P, ∀ x ∈ ball z (6 * r), ∀ y ∈ ball z (6 * r),
      internalMetric (fun x y => c ω * D ω x y) (ball z (6 * r)) x y = G ω x y)
    (hgreen : ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧
      ∀ᵐ ω ∂P, annulusGreenPotentialSup (a ω • μ ω) z (3 * r) (6 * r) = Y ω)
    (hmass : ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧
      ∀ᵐ ω ∂P, (a ω • μ ω) (rescaledSet U r z) = Y ω) :
    ∃ E : Set Ω, MeasurableSet[m] E ∧ ∀ᵐ ω ∂P,
      (pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z ↔ ω ∈ E) := by
  have hD' : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y => c ω * D ω x y) := by
    filter_upwards [hscale, hD] with ω hscale hD
    exact hD.const_mul hscale.1
  obtain ⟨E, hE, heq⟩ := @exists_local_pinchEvent_representative Ω mΩ P m
    (fun ω x y => c ω * D ω x y) (fun ω => a ω • μ ω) G U T Q' Q hconfig M z r hr
    hD' hG hGeq hgreen hmass
  refine ⟨E, hE, ?_⟩
  filter_upwards [hscale, heq] with ω hscale heq
  exact (pinchPointEventWithInternalBounds_const_mul (μ ω) (D ω) U T Q' Q M r z
    hscale.1 hscale.2.1 hscale.2.2).symm.trans heq


end HarmonicBalls
