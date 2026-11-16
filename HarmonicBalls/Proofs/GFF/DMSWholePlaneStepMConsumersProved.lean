import HarmonicBalls.Proofs.GFF.DMSWholePlaneMarkedChainProved
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmLambdaMeasurable

/-!
# The coded Palm identities for actual whole-plane fields

The coded Palm identity on the actual carrier `C(CircleDomain, ℝ)` in Ω-form
(`HarmonicBalls.palm_circle_omega_of_stepM`) and in λ-form (`HarmonicBalls.eq_r6_palm_circle_lambda_of_stepM`), and
the canonical-profile λ-form (`HarmonicBalls.eq_r6_palm_lambda_of_stepM_rawToProfile`), take the marked whole-plane
identity `StepM` as a hypothesis. That identity holds for every whole-plane GFF `(P, hC, hcirc)` and every `γ`-LQG
measure `μ` of it with `γ ∈ (0, 2)` and `α₀ = 0` (`HarmonicBalls.stepM_holds`). Applying each statement to it gives the
same statement for such fields with the range `0 < γ < 2` in place of the hypothesis `StepM`; no further input is
used. The canonical-profile statement keeps its hypothesis `RawToProfileStep`.

## Main statements

* `HarmonicBalls.IsWholePlaneGFF.palm_circle_omega`: the coded Palm identity on the actual carrier, Ω-form.
* `HarmonicBalls.IsWholePlaneGFF.eq_r6_palm_lambda_rawToProfile`: the canonical-profile λ-form.
* `HarmonicBalls.IsWholePlaneGFF.eq_r6_palm_circle_lambda`: the coded Palm identity on the actual carrier, λ-form.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

namespace IsWholePlaneGFF

/-- **The coded Palm identity, Ω-form, on the actual carrier, for actual whole-plane fields.** Let `γ ∈ (0, 2)`, let
`(P, hC, hcirc)` be a whole-plane GFF with `γ`-LQG measure `μ` (`α₀ = 0`), let `rho` be a literal mollifier and
`q : I → CircleDomain` a dense countable family, and let `F ω = circleCodedProfile hρ q (hC ω)` be the actual profile.
For a nonnegative jointly measurable `Ψ` on actual profiles times the marked point,
`∫_Ω ∫_{B_1} Ψ(F ω, z) (circleProfileMeasure γ 0 (F ω))(dz) dP
  = ∫_{B_1} ∫_Ω Ψ(circleDMSShiftFun γ z (F ω), z) dP d²z`. -/
theorem palm_circle_omega {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {I : Type*} [Countable I]
    (q : I → CircleDomain) (hq : DenseRange q)
    (Ψ : C(CircleDomain, ℝ) → ℂ → ℝ≥0∞) (hΨ : Measurable (fun p : C(CircleDomain, ℝ) × ℂ => Ψ p.1 p.2)) :
    ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (circleCodedProfile hρ q (hC ω)) z
        ∂(circleProfileMeasure γ 0 (circleCodedProfile hρ q (hC ω))) ∂P
      = ∫⁻ z in ball (0 : ℂ) 1,
          ∫⁻ ω, Ψ (circleDMSShiftFun γ z (circleCodedProfile hρ q (hC ω))) z ∂P ∂volume :=
  HarmonicBalls.palm_circle_omega_of_stepM hG hμ (stepM_holds P hγ0 hγ2 hC hcirc μ) hρ q hq Ψ hΨ

/-- **Canonical-profile λ-form of the coded Palm identity for actual whole-plane fields**, with `λ = Measure.map c P`,
for `γ ∈ (0, 2)`. It keeps the hypothesis `RawToProfileStep`. The λ-form on the actual carrier is
`HarmonicBalls.IsWholePlaneGFF.eq_r6_palm_circle_lambda`. -/
theorem eq_r6_palm_lambda_rawToProfile {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {c : Ω → CanonicalProfile} (hc : Measurable c)
    (hcJ : ∀ᵐ ω ∂P, ∀ p ∈ circleIndexSet, (c ω).1 p = hcirc ω p.1 p.2)
    (hB : RawToProfileStep P γ hC hcirc c)
    (Ψ : CanonicalProfile → ℂ → ℝ≥0∞) (hΨ : Measurable (fun p : CanonicalProfile × ℂ => Ψ p.1 p.2)) :
    ∫⁻ c', ∫⁻ z in ball (0 : ℂ) 1, Ψ c' z ∂(profileMeasure γ 0 c') ∂(Measure.map c P)
      = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ c', Ψ (shiftedProfile γ z c') z ∂(Measure.map c P) ∂volume :=
  HarmonicBalls.eq_r6_palm_lambda_of_stepM_rawToProfile hG hμ hc hcJ (stepM_holds P hγ0 hγ2 hC hcirc μ) hB Ψ hΨ

/-- **The coded Palm identity, λ-form on the actual carrier, for actual whole-plane fields.** With
`λ = Measure.map F P` the law of the actual profile `F ω = circleCodedProfile hρ q (hC ω)` and `γ ∈ (0, 2)`, for a
nonnegative jointly measurable `Ψ` on actual profiles times the marked point,
`∫ ∫_{B_1} Ψ(F, z) (circleProfileMeasure γ 0 F)(dz) λ(dF) = ∫_{B_1} ∫ Ψ(circleDMSShiftFun γ z F, z) λ(dF) d²z`. -/
theorem eq_r6_palm_circle_lambda {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {I : Type*} [Countable I]
    (q : I → CircleDomain) (hq : DenseRange q)
    (Ψ : C(CircleDomain, ℝ) → ℂ → ℝ≥0∞) (hΨ : Measurable (fun p : C(CircleDomain, ℝ) × ℂ => Ψ p.1 p.2)) :
    ∫⁻ F, ∫⁻ z in ball (0 : ℂ) 1, Ψ F z ∂(circleProfileMeasure γ 0 F)
        ∂(Measure.map (fun ω => circleCodedProfile hρ q (hC ω)) P)
      = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ F, Ψ (circleDMSShiftFun γ z F) z
          ∂(Measure.map (fun ω => circleCodedProfile hρ q (hC ω)) P) ∂volume :=
  HarmonicBalls.eq_r6_palm_circle_lambda_of_stepM hG hμ (stepM_holds P hγ0 hγ2 hC hcirc μ) hρ q hq Ψ hΨ

end IsWholePlaneGFF

end HarmonicBalls
