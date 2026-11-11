import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmStepM

/-! # The coded Palm identity in the λ-form (λ = the law of the actual profile)

The Ω-form of the coded Palm identity on the actual carrier is `palm_circle_omega_of_stepM` (PalmStepM.lean). This file
gives its λ-form, with `λ = Measure.map (circleCodedProfile hρ q ∘ hC) P` the law
of the actual profile: `eq_r6_palm_circle_lambda_of_stepM`. The only extra ingredient is the measurability of
`F ↦ ∫_{B_1} Ψ(F, z) circleProfileMeasure γ 0 F (dz)`, proved in CodedCirclePalm.lean from the kernel lemma
`measurable_lintegral_kernel_of_pointwise_finite` (Mathlib's `Measurable.lintegral_kernel_prod_right` needs an s-finite
kernel; the kernel `F ↦ (circleProfileMeasure γ 0 F).restrict B_1` is only pointwise finite).

The canonical-profile λ-form `eq_r6_palm_lambda_of_stepM_stepB_quarantined` is retained as QUARANTINED historical
evidence: it depends on the quarantined `RawToProfileStep`. Its helpers `profileMeasureBall` and
`measurable_profile_palm_lintegral` are kept for it.

Credit (Leonardo Bonanno): the Lattice-Probability LQG field modules `LatticeProb.Bonanno.LQGMetric.Field.*` (pinned
lean-v4.35 port) reach this file through `PalmStepM`; see the credit line in PalmStepM.lean.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- The coded LQG measure restricted to the unit disc, as a kernel on canonical profiles (`B_1` of the quarantined
λ-form). Each value is a finite measure (`profileMeasure` is locally finite and `B_1` is bounded). -/
def profileMeasureBall (γ : ℝ) : Kernel CanonicalProfile ℂ where
  toFun c' := (profileMeasure γ 0 c').restrict (ball (0 : ℂ) 1)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ (fun t ht => ?_)
    simp only [Measure.restrict_apply ht]
    exact (Measure.measurable_measure.mp (measurable_profileMeasure γ 0)) _ (ht.inter measurableSet_ball)

instance isFiniteMeasure_profileMeasureBall (γ : ℝ) (c' : CanonicalProfile) :
    IsFiniteMeasure (profileMeasureBall γ c') := by
  show IsFiniteMeasure ((profileMeasure γ 0 c').restrict (ball (0 : ℂ) 1))
  exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne

/-- Measurability in the canonical profile of `∫_{B_1} Ψ(c', z) profileMeasure γ 0 c'(dz)`, for jointly measurable `Ψ`. -/
theorem measurable_profile_palm_lintegral (γ : ℝ) {Ψ : CanonicalProfile → ℂ → ℝ≥0∞}
    (hΨ : Measurable (fun p : CanonicalProfile × ℂ => Ψ p.1 p.2)) :
    Measurable fun c' : CanonicalProfile => ∫⁻ z in ball (0 : ℂ) 1, Ψ c' z ∂(profileMeasure γ 0 c') :=
  measurable_lintegral_kernel_of_pointwise_finite (profileMeasureBall γ)
    (fun _ => inferInstance) (f := fun c' z => Ψ c' z) hΨ

/-- **Historical evidence, not used in the proof chain.** Canonical-profile λ-form, with
`λ = Measure.map c P`. It is derived from `RawToProfileStep` through
`palm_omega_of_stepM_stepB_quarantined`. The real λ-form is `eq_r6_palm_circle_lambda_of_stepM`. -/
theorem eq_r6_palm_lambda_of_stepM_stepB_quarantined {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {c : Ω → CanonicalProfile} (hc : Measurable c)
    (hcJ : ∀ᵐ ω ∂P, ∀ p ∈ circleIndexSet, (c ω).1 p = hcirc ω p.1 p.2)
    (hM : StepM P γ hC hcirc μ) (hB : RawToProfileStep P γ hC hcirc c)
    (Ψ : CanonicalProfile → ℂ → ℝ≥0∞) (hΨ : Measurable (fun p : CanonicalProfile × ℂ => Ψ p.1 p.2)) :
    ∫⁻ c', ∫⁻ z in ball (0 : ℂ) 1, Ψ c' z ∂(profileMeasure γ 0 c') ∂(Measure.map c P)
      = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ c', Ψ (shiftedProfile γ z c') z ∂(Measure.map c P) ∂volume := by
  have hR : ∀ z : ℂ, ∫⁻ c', Ψ (shiftedProfile γ z c') z ∂(Measure.map c P)
      = ∫⁻ ω, Ψ (shiftedProfile γ z (c ω)) z ∂P := by
    intro z
    have hs : Measurable fun c' : CanonicalProfile => shiftedProfile γ z c' :=
      (measurable_shiftedProfile γ).comp (measurable_id.prodMk measurable_const)
    exact lintegral_map (hΨ.comp (hs.prodMk measurable_const)) hc
  rw [lintegral_map (measurable_profile_palm_lintegral γ hΨ) hc]
  simp_rw [hR]
  exact palm_omega_of_stepM_stepB_quarantined hG hμ hcJ hM hB Ψ hΨ

/-- **The coded Palm identity, λ-form on the actual carrier.** With `λ = Measure.map F P` the law of the actual
profile `F ω = circleCodedProfile hρ q (hC ω)`, for a nonnegative jointly measurable `Ψ` on actual profiles times the
marked point, `∫ ∫_{B_1} Ψ(F, z) (circleProfileMeasure γ 0 F)(dz) λ(dF) = ∫_{B_1} ∫ Ψ(circleDMSShiftFun γ z F, z) λ(dF) d²z`.
Derived from `palm_circle_omega_of_stepM` (PalmStepM.lean), by the transport of the Ω-identity along the pushforward. -/
theorem eq_r6_palm_circle_lambda_of_stepM {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hM : StepM P γ hC hcirc μ)
    {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {I : Type*} [Countable I]
    (q : I → CircleDomain) (hq : DenseRange q)
    (Ψ : C(CircleDomain, ℝ) → ℂ → ℝ≥0∞) (hΨ : Measurable (fun p : C(CircleDomain, ℝ) × ℂ => Ψ p.1 p.2)) :
    ∫⁻ F, ∫⁻ z in ball (0 : ℂ) 1, Ψ F z ∂(circleProfileMeasure γ 0 F)
        ∂(Measure.map (fun ω => circleCodedProfile hρ q (hC ω)) P)
      = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ F, Ψ (circleDMSShiftFun γ z F) z
          ∂(Measure.map (fun ω => circleCodedProfile hρ q (hC ω)) P) ∂volume := by
  have hc : Measurable fun ω => circleCodedProfile hρ q (hC ω) :=
    ((circleCompatDecoder_gff_identification rho hρ q hq).2.2.2.2.2.2 hG).1
  have hR : ∀ z : ℂ, ∫⁻ F, Ψ (circleDMSShiftFun γ z F) z
      ∂(Measure.map (fun ω => circleCodedProfile hρ q (hC ω)) P)
        = ∫⁻ ω, Ψ (circleDMSShiftFun γ z (circleCodedProfile hρ q (hC ω))) z ∂P := by
    intro z
    have hs : Measurable fun F : C(CircleDomain, ℝ) => (circleDMSShiftFun γ z F, z) :=
      ((measurable_circleDMSShiftFun_fixedGamma γ).comp (measurable_id.prodMk measurable_const)).prodMk
        measurable_const
    exact lintegral_map (hΨ.comp hs) hc
  rw [lintegral_map (measurable_circle_palm_lintegral γ hΨ) hc]
  simp_rw [hR]
  exact palm_circle_omega_of_stepM hG hμ hM hρ q hq Ψ hΨ

end HarmonicBalls

end
