import HarmonicBalls.Proofs.Sec11.PinchContinuousObservation

/-! # Common measurable representatives of pinch observations -/

namespace HarmonicBalls

open MeasureTheory Filter Set

/-- Two almost surely length-metric observations have a common measurable
pinch-event representative. The observations need not have the same law. -/
theorem exists_common_pinchEvent_representative_of_continuous_observations
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ₀ μ₁ : Ω → Measure ℂ) (D₀ D₁ : Ω → C(ℂ × ℂ, ℝ))
    {U T Q V : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q V)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hD₀ : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y => D₀ ω (x, y)))
    (hD₁ : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y => D₁ ω (x, y))) :
    ∃ A : Set (Measure ℂ × C(ℂ × ℂ, ℝ)), MeasurableSet A ∧
      (∀ᵐ ω ∂P, (pinchPointEventWithInternalBounds (μ₀ ω) (fun x y => D₀ ω (x, y))
        U T Q V M r z ↔ (μ₀ ω, D₀ ω) ∈ A)) ∧
      (∀ᵐ ω ∂P, (pinchPointEventWithInternalBounds (μ₁ ω) (fun x y => D₁ ω (x, y))
        U T Q V M r z ↔ (μ₁ ω, D₁ ω) ∈ A)) := by
  let e₀ : Ω → Ω ⊕ Ω := Sum.inl
  let e₁ : Ω → Ω ⊕ Ω := Sum.inr
  have he₀ : MeasurableEmbedding e₀ := ⟨Sum.inl_injective, measurable_inl, fun {_} h => h.inl_image⟩
  have he₁ : MeasurableEmbedding e₁ := ⟨Sum.inr_injective, measurable_inr, fun {_} h => h.inr_image⟩
  let S : Measure (Ω ⊕ Ω) := P.map e₀ + P.map e₁
  let μ : Ω ⊕ Ω → Measure ℂ := Sum.elim μ₀ μ₁
  let D : Ω ⊕ Ω → C(ℂ × ℂ, ℝ) := Sum.elim D₀ D₁
  have hD : ∀ᵐ s ∂S, IsEuclideanLengthMetric (fun x y => D s (x, y)) := by
    apply ae_add_measure_iff.mpr
    exact ⟨he₀.ae_map_iff.mpr hD₀, he₁.ae_map_iff.mpr hD₁⟩
  obtain ⟨A, hA, hEq⟩ :=
    exists_pinchEvent_representative_of_continuous_observation S μ D hconfig M z hr hD
  have hh := ae_add_measure_iff.mp hEq
  exact ⟨A, hA, he₀.ae_map_iff.mp hh.1, he₁.ae_map_iff.mp hh.2⟩


end HarmonicBalls
