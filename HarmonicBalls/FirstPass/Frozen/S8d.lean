import HarmonicBalls.Proofs.GFF.CommonContinuousCircleLQGVersion
import HarmonicBalls.Proofs.Sec8.PhaseTorus
import HarmonicBalls.Defs.LQG
import HarmonicBalls.FirstPass.S8c.TorusTail

/-! # FIRST-PASS frozen inputs of the Lemma 8.2 route (fp-S8d, owner n4)

Two EXTERNAL facts approved by the operator (inbox wave 7, 2026-11-09, item n4): they are general GMC and ergodic-theory
facts, not statements about this paper's clusters, odometers, harmonic balls or IDLA processes. Each is stated in the
weakest form used by the profile instance of `LocalPhaseTailStep` (`FirstPass/S8d.lean`, to come). -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- FIRST-PASS FROZEN. Profile-level measurability of the γ-LQG measure. For a whole-plane GFF `(P, hC, hcirc)` with
a measurable, almost surely continuous circle-average profile `F` (versions of `hcirc`), and the γ-LQG measure `μ` of
parameter `α` (`IsLQGMeasureOfField`), there is a measurable map `Dec` from continuous circle profiles to measures on `ℂ`
such that `μ = Dec ∘ F` almost surely, and for the image law `P.map F`, almost every profile `y` is the vague limit of
its approximations `ε^{γ²/2} e^{γ ŷ_ε(z)} dz` along the dyadic scales, with `ŷ_ε(z) = fieldCircleAverage α (circleProfile y)`.
In words: the LQG measure is a measurable function of the circle-average profile (Duplantier–Sheffield, LQG and KPZ,
arXiv:0808.1560; Duplantier–Sheffield 2011, Prop. 1.1 for the vague limit). The repository proves only the Ω-level
measurability (Proofs/Sec5/OpenMeasureLaw.lean:130 `IsWholePlaneGFF.aemeasurable_lqgMeasure`), not this profile form.
Source locator: standard; locator pending. Used by: firstPass_8_2 (through FirstPass/S8d.lean, the profile instance). -/
def LQGMeasureOfProfileMeasurableFrozen : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (F : Ω → C(CircleParameter, ℝ)),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ → Measurable F →
    (∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2) →
    ∃ Dec : C(CircleParameter, ℝ) → Measure ℂ, Measurable Dec ∧
      (∀ᵐ ω ∂P, μ ω = Dec (F ω)) ∧
      (∀ᵐ y ∂(P.map F), IsLQGLimit γ (fieldCircleAverage α (circleProfile y)) (Dec y))

/-- FIRST-PASS FROZEN. Product ergodicity of the doubling map with an ergodic measure-preserving map. For a probability
space `(Y, ν)` with a measure-preserving ergodic map `T`, the map `(θ, y) ↦ (2θ, T y)` on the phase torus times `Y` is
ergodic for the product of the uniform phase measure with `ν`. The doubling map on the torus is mixing (hence weakly
mixing), and the product of a weakly mixing map with an ergodic map is ergodic (Walters, An Introduction to Ergodic
Theory, GTM 79, §1.6 and Thm 1.27). Mathlib has no such product lemma (checked: no `Ergodic` product lemma under
`Mathlib/Dynamics/Ergodic`). Source locator: standard; locator pending. Used by: firstPass_8_2 (the phase tail of
FirstPass/S8d.lean, through `ae_frequency_of_torus_dilation`). -/
def PhaseTorusDoublingProductErgodicFrozen : Prop :=
  ∀ (Y : Type u) [MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν] (T : Y → Y),
    MeasurePreserving T ν ν → Ergodic T ν →
    Ergodic (fun p : PhaseTorus × Y => (phaseTorusDouble p.1, T p.2)) (phaseTorusFieldMeasure ν)

/-- FIRST-PASS FROZEN. Uniqueness of the Radon measure representing its integrals on continuous compactly supported
functions (the uniqueness part of the Riesz representation theorem on the locally compact space `ℂ`). For locally finite
measures `m, m'` on `ℂ`, if `∫ f dm = ∫ f dm'` for all continuous compactly supported real `f`, then `m = m'`. Source:
Rudin, Real and Complex Analysis, 3rd ed., Thm 2.14; standard general measure theory, not specific to this paper;
locator pending (exact numbering to be checked against the edition). Used by: firstPass_8_2 (through the uniqueness of the
vague limit `isLQGLimit_unique`, FirstPass/S8d/LQGLimitUnique.lean, in the identification of the dilated LQG measure). -/
def RadonIntegralUniqueFrozen : Prop :=
  ∀ (m m' : Measure ℂ), IsLocallyFiniteMeasure m → IsLocallyFiniteMeasure m' →
    (∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → ∫ z, f z ∂m = ∫ z, f z ∂m') → m = m'

end HarmonicBalls
