import HarmonicBalls.Proofs.Potential.GreenOccupationBoundary
import HarmonicBalls.FirstPass.Phase2.GreenPotentialHolderHolds

/-! # A canonical killed Brownian occupation density

The zero-diagonal extension of twice the Green kernel represents the killed
occupation measure at every starting point and is continuous off its pole.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace HarmonicBalls.GreenOccupation

/-- Twice the Green kernel is a continuous off-pole density of the killed
occupation measure, with value zero on the pole and outside the domain. -/
theorem green_occupation_density {D : Set ℂ} (hD : IsSmoothBoundedOpen D) (x : ℂ) :
    AEMeasurable (fun y => ENNReal.ofReal (2 * greenFunction D x y)) volume ∧
    ContinuousOn (fun y => ENNReal.ofReal (2 * greenFunction D x y)) (D \ {x}) ∧
    volume.withDensity (fun y => ENNReal.ofReal (2 * greenFunction D x y)) =
      occupationMeasure D (GreenGeneral.isOpen_of_isSmoothBoundedOpen hD) x ∧
    ENNReal.ofReal (2 * greenFunction D x x) = 0 ∧
    ∀ y ∉ D, ENNReal.ofReal (2 * greenFunction D x y) = 0 := by
  let hDo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  refine ⟨((integrable_greenFunction_pole hDo hD.1 x).const_mul 2).aestronglyMeasurable.aemeasurable.ennreal_ofReal, ?_, ?_, ?_, ?_⟩
  · by_cases hx : x ∈ D
    · intro y hy
      have hxy : x ≠ y := by simpa using Ne.symm (show y ≠ x by simpa using hy.2)
      have hc := continuousAt_greenFunction_uncurry hDo hD.1 hx hy.1 hxy
      exact (ENNReal.continuous_ofReal.continuousAt.comp
        (continuousAt_const.mul (hc.comp (continuousAt_const.prodMk continuousAt_id)))).continuousWithinAt
    · have hz : (fun y => ENNReal.ofReal (2 * greenFunction D x y)) = fun _ => 0 := by
        funext y
        simp [greenFunction, hx]
      rw [hz]
      exact continuousOn_const
  · exact (occupationMeasure_eq_greenMeasure_all hD x).symm
  · simp [greenFunction]
  · intro y hy
    simp [greenFunction, hy]

universe u

/-- On the Green-potential event, the canonical occupation density has an
integrable Liouville potential for every starting point in the closure. -/
theorem lqg_green_occupation_density_potential {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hLQG : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ D : Set ℂ, (hD : IsSmoothBoundedOpen D) →
      ∀ f : ℂ → ℝ, MemLp f ⊤ ((μ ω).restrict (closure D)) →
        (∃ C r : ℝ≥0, 0 < r ∧
          HolderOnWith C r (fun x => ∫ y in D, greenFunction D x y * f y ∂(μ ω)) (closure D)) ∧
        ∀ x ∈ closure D,
          IntegrableOn (fun y => (ENNReal.ofReal (2 * greenFunction D x y)).toReal * f y) D (μ ω) ∧
          (∫ y in D, (ENNReal.ofReal (2 * greenFunction D x y)).toReal * f y ∂(μ ω)) =
            2 * ∫ y in D, greenFunction D x y * f y ∂(μ ω) := by
  have hp := greenPotentialHolderStmt_holds γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hLQG
  filter_upwards [hp] with ω hp
  intro D hD f hf
  refine ⟨(hp D hD f hf).2, ?_⟩
  intro x hx
  have heq : (fun y => (ENNReal.ofReal (2 * greenFunction D x y)).toReal * f y) =
      (fun y => 2 * (greenFunction D x y * f y)) := by
    funext y
    rw [ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (greenFunction_nonneg hD.1 x y))]
    ring
  rw [heq]
  exact ⟨((hp D hD f hf).1 x hx).const_mul 2, integral_const_mul 2 _⟩

end HarmonicBalls.GreenOccupation
