import HarmonicBalls.Proofs.Sec11.LQGSingularMetricObservable
import HarmonicBalls.Proofs.Sec2.Mixture
import HarmonicBalls.Steps.Sec11.GFFMeasurePreserving

/-! # A common singular metric observable on a mixture

A positive-weight mixture provides one measurable decoder for countably many
whole-plane GFFs, provided their singular metrics use the same base functional.
The singular-field metric axioms on the mixture are staged literature inputs.
-/

namespace HarmonicBalls
open MeasureTheory ProbabilityTheory

/-- An almost-sure property of the mixture holds on every positive-weight slice. -/
theorem ae_slice_of_ae_mix {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [SFinite P] {p : ℕ → Ω → Prop}
    (h : ∀ᵐ x ∂(mixMeasure.prod P), p x.1 x.2) (k : ℕ) :
    ∀ᵐ ω ∂P, p k ω := by
  rw [ae_iff] at h ⊢
  apply le_antisymm
  · calc
      P {ω | ¬ p k ω} ≤
          ENNReal.ofReal (mixMass.toReal * ((k : ℝ) + 1) ^ 2) *
            (mixMeasure.prod P) {x | ¬ p x.1 x.2} :=
        measure_slice_le (P := P) {x | ¬ p x.1 x.2} k
      _ = 0 := by rw [h, mul_zero]
  · exact zero_le

/-- Countably many GFFs on one probability space admit a common singular metric
observable when the same base metric functional generates all their distances.
The staged singular-field metric axioms are assumed on the mixture itself. -/
theorem exists_common_singularMetric_observable_of_mixture
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    (hC : ℕ → Ω → (ℂ → ℝ) → ℝ) (hcirc : ℕ → Ω → ℝ → ℂ → ℝ)
    (D : ℕ → Ω → C(ℂ × ℂ, ℝ))
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (hgff : ∀ k, IsWholePlaneGFF P (hC k) (hcirc k))
    (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ k, ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D k ω (u, v) ∧
      ENNReal.ofReal (D k ω (u, v)) =
        weylScaling (𝔇 (hC k ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v)
    (haxioms : LQGMetricFieldAxioms (mixMeasure.prod P) γ ξ α₀
      (fun x => hC x.1 x.2) (fun x => hcirc x.1 x.2))
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ) :
    ∃ F : (GFFObservable.Admissible → ℝ) → C(ℂ × ℂ, ℝ), Measurable F ∧
      ∀ k, ∀ᵐ ω ∂P,
        F (fun o => o.1.eval (hC k ω) (hcirc k ω)) = D k ω := by
  let _ := (hgff 0).isProbabilityMeasure
  have hmix : IsWholePlaneGFF (mixMeasure.prod P)
      (fun x => hC x.1 x.2) (fun x => hcirc x.1 x.2) :=
    wholePlaneGFFMixtureStep_holds Ω P hC hcirc mixMeasure inferInstance hgff
  have hDm : IsLQGMetricOfField (mixMeasure.prod P) γ ξ α₀
      (fun x => hC x.1 x.2) (fun x u v => D x.1 x.2 (u, v)) :=
    ⟨𝔇, h𝔇, ae_mix_of_forall hD⟩
  obtain ⟨F, hF, hEq⟩ := hmix.exists_singularMetric_observable
    haxioms hγ hγ₂ hα hDm
  refine ⟨F, hF, fun k => ?_⟩
  exact ae_slice_of_ae_mix (P := P)
    (p := fun k ω => F (fun o => o.1.eval (hC k ω) (hcirc k ω)) = D k ω) hEq k


end HarmonicBalls
