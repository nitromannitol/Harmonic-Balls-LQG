import HarmonicBalls.Proofs.Potential.GreenOccupationCharacterization
import HarmonicBalls.FirstPass.Phase2.NonatomicHolds
import HarmonicBalls.FirstPass.Phase2.GreenPotentialHolderHolds

/-! # Occupation densities and Liouville Green potentials

A continuous off-pole occupation density has an integrable potential against
Liouville measure, on the same event as the Green-potential regularity theorem.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace HarmonicBalls.GreenOccupation

universe u

/-- On one event, every continuous off-pole occupation density has a potential
against the Liouville measure equal to twice the Green potential. -/
theorem lqg_occupation_density_potential {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hLQG : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ D : Set ℂ, (hD : IsSmoothBoundedOpen D) →
      ∀ f : ℂ → ℝ, MemLp f ⊤ ((μ ω).restrict (closure D)) →
        (∃ C r : ℝ≥0, 0 < r ∧
          HolderOnWith C r (fun x => ∫ y in D, greenFunction D x y * f y ∂(μ ω)) (closure D)) ∧
        ∀ x ∈ D, ∀ k : ℂ → ℝ≥0∞, AEMeasurable k volume →
          ContinuousOn k (D \ {x}) →
          volume.withDensity k = occupationMeasure D (GreenGeneral.isOpen_of_isSmoothBoundedOpen hD) x →
            IntegrableOn (fun y => (k y).toReal * f y) D (μ ω) ∧
            (∫ y in D, (k y).toReal * f y ∂(μ ω)) =
              2 * ∫ y in D, greenFunction D x y * f y ∂(μ ω) := by
  have hn := lqgMeasureNonatomic_holds Ω P γ α₀ hC hcirc hGFF hγ hγ2 hα μ hLQG
  have hp := greenPotentialHolderStmt_holds γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hLQG
  filter_upwards [hn, hp] with ω hn hp
  intro D hD f hf
  refine ⟨(hp D hD f hf).2, ?_⟩
  intro x hx k hk hkc hkocc
  have ht := occupation_density_potential_eq_green hD hx hk hkc hkocc (μ ω) (hn x) f
  have hi := ((hp D hD f hf).1 x (subset_closure hx)).const_mul (2 : ℝ)
  refine ⟨ht.1.mpr ?_, ht.2⟩
  simpa only [IntegrableOn, mul_assoc] using hi

end HarmonicBalls.GreenOccupation
