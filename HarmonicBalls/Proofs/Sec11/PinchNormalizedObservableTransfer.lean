import HarmonicBalls.Proofs.Sec11.PinchContinuousObservation
import HarmonicBalls.Proofs.Sec11.PinchNormalizedRestriction

/-! # Transfer through normalized continuous metric-measure observations -/

namespace HarmonicBalls
open Set Metric MeasureTheory Filter
open scoped ENNReal

/-- Absolute continuity transfers pinch-event positivity through jointly
observed normalized restrictions and independently scaled metrics. -/
theorem positive_pinchEvent_of_normalized_observable_ac
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {U T Q' Q B : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r) (hB : ball z (6 * r) ⊆ B)
    (μ ν : Ω → Measure ℂ) (D E : Ω → ℂ → ℂ → ℝ)
    (X Y : Ω → Measure ℂ × C(ℂ × ℂ, ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (c d : Ω → ℝ)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hXeq : ∀ᵐ ω ∂P, 0 < c ω ∧ μ ω B ≠ 0 ∧ μ ω B ≠ ∞ ∧
      (X ω).1 = normalizedRestriction (μ ω) B ∧
      ∀ x y, (X ω).2 (x, y) = c ω * D ω x y)
    (hYeq : ∀ᵐ ω ∂P, 0 < d ω ∧ ν ω B ≠ 0 ∧ ν ω B ≠ ∞ ∧
      (Y ω).1 = normalizedRestriction (ν ω) B ∧
      ∀ x y, (Y ω).2 (x, y) = d ω * E ω x y)
    (hac : P.map Y ≪ P.map X)
    (hp : 0 < P {ω | pinchPointEventWithInternalBounds (ν ω) (E ω) U T Q' Q M r z}) :
    0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z} := by
  let e₀ : Ω → Ω ⊕ Ω := Sum.inl
  let e₁ : Ω → Ω ⊕ Ω := Sum.inr
  have he₀ : MeasurableEmbedding e₀ := ⟨Sum.inl_injective, measurable_inl, fun {_} hs => hs.inl_image⟩
  have he₁ : MeasurableEmbedding e₁ := ⟨Sum.inr_injective, measurable_inr, fun {_} hs => hs.inr_image⟩
  let S : Measure (Ω ⊕ Ω) := P.map e₀ + P.map e₁
  let Z : Ω ⊕ Ω → Measure ℂ × C(ℂ × ℂ, ℝ) := Sum.elim X Y
  have hxlen : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y => (X ω).2 (x, y)) := by
    filter_upwards [hD, hXeq] with ω hd hx
    have heq : (fun x y => (X ω).2 (x, y)) = fun x y => c ω * D ω x y := by
      funext x y; exact hx.2.2.2.2 x y
    rw [heq]
    exact hd.const_mul hx.1
  have hylen : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y => (Y ω).2 (x, y)) := by
    filter_upwards [hE, hYeq] with ω hd hx
    have heq : (fun x y => (Y ω).2 (x, y)) = fun x y => d ω * E ω x y := by
      funext x y; exact hx.2.2.2.2 x y
    rw [heq]
    exact hd.const_mul hx.1
  have hzlen : ∀ᵐ s ∂S, IsEuclideanLengthMetric (fun x y => (Z s).2 (x, y)) := by
    apply ae_add_measure_iff.mpr
    exact ⟨he₀.ae_map_iff.mpr hxlen, he₁.ae_map_iff.mpr hylen⟩
  obtain ⟨A, hA, ha⟩ := exists_pinchEvent_representative_of_continuous_observation S
    (fun s => (Z s).1) (fun s => (Z s).2) hconfig M z hr hzlen
  have ha' := ae_add_measure_iff.mp ha
  have haX := he₀.ae_map_iff.mp ha'.1
  have haY := he₁.ae_map_iff.mp ha'.2
  have ex : {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z} =ᵐ[P] X ⁻¹' A := by
    filter_upwards [hD, hXeq, haX] with ω hd hx ha
    have hn := pinchPointEventWithInternalBounds_normalizedRestriction hd hconfig M z hr hx.1 hB hx.2.1 hx.2.2.1
    have heq : (fun x y => (X ω).2 (x, y)) = fun x y => c ω * D ω x y := by
      funext x y; exact hx.2.2.2.2 x y
    change pinchPointEventWithInternalBounds (X ω).1 (fun x y => (X ω).2 (x, y)) U T Q' Q M r z ↔ X ω ∈ A at ha
    rw [hx.2.2.2.1, heq] at ha
    exact propext (hn.symm.trans ha)
  have ey : {ω | pinchPointEventWithInternalBounds (ν ω) (E ω) U T Q' Q M r z} =ᵐ[P] Y ⁻¹' A := by
    filter_upwards [hE, hYeq, haY] with ω hd hx ha
    have hn := pinchPointEventWithInternalBounds_normalizedRestriction hd hconfig M z hr hx.1 hB hx.2.1 hx.2.2.1
    have heq : (fun x y => (Y ω).2 (x, y)) = fun x y => d ω * E ω x y := by
      funext x y; exact hx.2.2.2.2 x y
    change pinchPointEventWithInternalBounds (Y ω).1 (fun x y => (Y ω).2 (x, y)) U T Q' Q M r z ↔ Y ω ∈ A at ha
    rw [hx.2.2.2.1, heq] at ha
    exact propext (hn.symm.trans ha)
  rw [measure_congr ey, ← Measure.map_apply hY hA] at hp
  rw [measure_congr ex, ← Measure.map_apply hX hA]
  by_contra hn
  exact (ne_of_gt hp) (hac (nonpos_iff_eq_zero.mp (not_lt.mp hn)))

end HarmonicBalls
