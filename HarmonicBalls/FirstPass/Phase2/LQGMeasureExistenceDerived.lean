import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import LatticeProb.LQG.LQGMeasureExistenceProved

/-!
# Existence of the γ-LQG measure with an `α₀`-log singularity, derived

`LQGMeasureExistence` (Proposed/LQG.lean:74; arXiv:2208.11795v3, Proposition 1.1, p. 9) as a theorem, for every
probability space, every `γ` and every `α₀`: the library proves the LP form
`LatticeProb.LQG.lqgMeasureExistenceLP_proved` (the γ-LQG measure of the whole-plane Gaussian free field plus
`α₀ log(1/|·|)`, as the a.s. vague limit of the circle-average approximations along the dyadic scales, for
`0 < γ < 2` and `α₀ < Q`), and the bridge equivalences `LPBridge.isWholePlaneGFF_iff` (M1) and
`LPBridge.isLQGMeasureOfField_iff` (M4) transport it to the HB definitions. This is the reverse of
`lqgMeasureExistenceLP_of_HB` (Phase2/DerivedInputs30.lean).
-/

open MeasureTheory

universe u

namespace HarmonicBalls

/-- **Proposition 1.1 of arXiv:2208.11795 (existence of the LQG measure), derived.** `LQGMeasureExistence` holds
for every probability space, every `γ` and every `α₀`. -/
theorem lqgMeasureExistence_derived {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    LQGMeasureExistence P γ α₀ hC hcirc := by
  intro hG hγ hγ2 hα
  obtain ⟨μ, hμ⟩ := LatticeProb.LQG.lqgMeasureExistenceLP_proved P γ α₀ hC hcirc
    ((LPBridge.isWholePlaneGFF_iff P hC hcirc).1 hG) hγ hγ2 hα
  exact ⟨μ, (LPBridge.isLQGMeasureOfField_iff P γ α₀ hcirc μ).2 hμ⟩

/-- `LQGMeasureExistence` for every probability space, field and pair `(γ, α)`, in the binder order
`Ω, P, γ, α, hC, hcirc` of the hypotheses `hE` of the closure theorems. -/
theorem lqgMeasureExistence_forall_field : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc :=
  fun _ _ P γ α hC hcirc => lqgMeasureExistence_derived P γ α hC hcirc

/-- `LQGMeasureExistence` in the binder order `γ, α₀, Ω, P, hC, hcirc`. -/
theorem lqgMeasureExistence_forall_exponents : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α₀ hC hcirc :=
  fun γ α₀ _ _ P hC hcirc => lqgMeasureExistence_derived P γ α₀ hC hcirc

/-- `LQGMeasureExistence` without singularity (`α₀ = 0`), in the binder order `γ, Ω, P, hC, hcirc`. -/
theorem lqgMeasureExistence_forall_zero : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc :=
  fun γ _ _ P hC hcirc => lqgMeasureExistence_derived P γ 0 hC hcirc

end HarmonicBalls
