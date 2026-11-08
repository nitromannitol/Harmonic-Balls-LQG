import Mathlib
import HarmonicBalls.Proposed.DuplantierMillerSheffield

/-! # Route (A), Palm identity: the total mass of the marked whole-plane measure (eq:r9-total-area of r10)

The printed unnormalized whole-plane clause of [DMS, Lemma A.10, p. 184] (`DMSLemmaA10WholePlaneUnnormalized`,
DuplantierMillerSheffield.lean) tested against the constant function one gives `E[μ_g(B_1)] = π`
(r10 `eq:r9-total-area`, line 2613). This is the first-moment input of the marked identity `l:r9-marked`
(r10 lines 2575-2790), which replaces the named Step M of PalmStepM.lean.
-/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

/-- **eq:r9-total-area** (r10 line 2613): `E[μ_g(B_1)] = π`, obtained from the printed unnormalized whole-plane
identity of [DMS, Lemma A.10, p. 184] with test function one. -/
theorem integral_measure_ball_eq_pi {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hU : DMSLemmaA10WholePlaneUnnormalized P γ hC hcirc μ)
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∫ ω, (μ ω (ball 0 1)).toReal ∂P = Real.pi := by
  have h := hU hG hμ (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by simp⟩
  simpa [integral_const, setIntegral_const, Complex.volume_ball, Measure.real] using h

end HarmonicBalls

end
