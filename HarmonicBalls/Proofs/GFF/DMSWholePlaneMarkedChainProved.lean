import HarmonicBalls.Proofs.GFF.DMSWholePlaneConsumers
import HarmonicBalls.Proofs.Sec11.ClosureScales.MarkedL1
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmStepMDMS

/-!
# The marked whole-plane chain heads for actual whole-plane fields

The marked chain heads `HarmonicBalls.tendsto_integral_abs_marked_sub` and `HarmonicBalls.stepM_of_dms` take the
unnormalized whole-plane clause of [DMS, Lemma A.10, p. 184] (`DMSLemmaA10WholePlaneUnnormalized`) as a hypothesis.
That clause holds for every whole-plane GFF `(P, hC, hcirc)` and every `γ`-LQG measure `μ` of it with `γ ∈ (0, 2)`
and `α₀ = 0` (`dmsLemmaA10WholePlaneUnnormalized_holds`). Applying the heads to it gives both statements for such
fields with the range `0 < γ < 2` in place of the clause; no further input is used.

## Main statements

* `HarmonicBalls.stepM_holds`: the marked whole-plane identity `StepM`.
* `HarmonicBalls.IsWholePlaneGFF.tendsto_integral_abs_marked_sub`: `E |μ_{2^(-k)}(η) - μ_h(η)| → 0` for
  `0 ≤ η ∈ C_c(B_1)`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Filter Topology

/-- **Step M for actual whole-plane fields**: for `γ ∈ (0, 2)`, every whole-plane GFF `(P, hC, hcirc)` and every
`γ`-LQG measure `μ` of it with `α₀ = 0`, the marked whole-plane identity `StepM` holds. -/
theorem stepM_holds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) :
    StepM P γ hC hcirc μ :=
  stepM_of_dms (dmsLemmaA10WholePlaneUnnormalized_holds P hγ0 hγ2 hC hcirc μ)

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {γ : ℝ}

/-- **L¹ convergence of the marked LQG masses for actual whole-plane fields**: for `γ ∈ (0, 2)`, a whole-plane
GFF and a `γ`-LQG measure `μ` of it with `α₀ = 0`, and `0 ≤ η ∈ C_c(B_1)`, `E|μ_{2^(-k)}(η) - μ_h(η)| → 0`. -/
theorem tendsto_integral_abs_marked_sub (hG : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) {η : ℂ → ℝ} (hη : Continuous η)
    (hηs : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z) (htsupp : tsupport η ⊆ ball (0 : ℂ) 1) :
    Tendsto (fun k : ℕ => ∫ ω, |(∫ z, η z * (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω (dyadicScale k) z)) ∂(volume : Measure ℂ)) - ∫ z, η z ∂(μ ω)| ∂P)
      atTop (𝓝 0) :=
  have := hG.isProbabilityMeasure
  HarmonicBalls.tendsto_integral_abs_marked_sub γ hG hμ
    (dmsLemmaA10WholePlaneUnnormalized_holds P hγ0 hγ2 hC hcirc μ) hη hηs hη0 htsupp

end IsWholePlaneGFF

end HarmonicBalls
