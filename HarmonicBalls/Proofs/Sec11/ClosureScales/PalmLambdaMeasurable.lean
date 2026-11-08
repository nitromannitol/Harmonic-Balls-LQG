import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmStepM

/-! # Route (A), eq:r6-palm in the λ-form (λ = the law of the canonical profile)

The Ω-form of the coded Palm identity is `palm_omega_of_stepM_stepB` (PalmStepM.lean). This file gives its λ-form,
eq:r6-palm of the r8 text (line 1815), with `λ = Measure.map c P`. The only extra ingredient is the measurability of
`c' ↦ ∫_{B_1} Ψ(c', z) profileMeasure γ 0 c'(dz)`. Mathlib's `Measurable.lintegral_kernel_prod_right` needs an
s-finite kernel; the kernel `c' ↦ (profileMeasure γ 0 c').restrict B_1` is only pointwise finite, and the proof of
Mathlib's lemma goes through with `Kernel.measurable_kernel_prodMk_left_of_finite`, which needs only pointwise finiteness
(the same monotone-class argument: simple-function approximation and monotone convergence).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- Auxiliary: measurability of `a ↦ ∫⁻ b, 1_t(a, b) c ∂κ a` for a kernel with pointwise finite values. -/
theorem measurable_lintegral_indicator_const_of_pointwise_finite {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (κ : Kernel α β) (hκ : ∀ a, IsFiniteMeasure (κ a)) {t : Set (α × β)}
    (ht : MeasurableSet t) (c : ℝ≥0∞) :
    Measurable fun a => ∫⁻ b, t.indicator (Function.const (α × β) c) (a, b) ∂κ a := by
  unfold Function.const
  simp_rw [lintegral_indicator_const_comp measurable_prodMk_left ht _]
  exact Measurable.const_mul (Kernel.measurable_kernel_prodMk_left_of_finite ht hκ) c

/-- Measurability of a parametric lower integral against a kernel whose values are finite measures (pointwise
finiteness suffices). The proof is that of Mathlib's `Measurable.lintegral_kernel_prod_right`
(`Probability/Kernel/MeasurableLIntegral.lean`), with the indicator case replaced by the pointwise-finite version. -/
theorem measurable_lintegral_kernel_of_pointwise_finite {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (κ : Kernel α β) (hκ : ∀ a, IsFiniteMeasure (κ a)) {f : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) : Measurable fun a => ∫⁻ b, f a b ∂κ a := by
  let F : ℕ → SimpleFunc (α × β) ℝ≥0∞ := SimpleFunc.eapprox (Function.uncurry f)
  have h : ∀ a, ⨆ n, F n a = Function.uncurry f a := SimpleFunc.iSup_eapprox_apply hf
  simp only [Prod.forall, Function.uncurry_apply_pair] at h
  simp_rw [← h]
  have : ∀ a, (∫⁻ b, ⨆ n, F n (a, b) ∂κ a) = ⨆ n, ∫⁻ b, F n (a, b) ∂κ a := by
    intro a
    rw [lintegral_iSup]
    · exact fun n => (F n).measurable.comp measurable_prodMk_left
    · exact fun i j hij b => SimpleFunc.monotone_eapprox (Function.uncurry f) hij _
  simp_rw [this]
  refine .iSup fun n => ?_
  refine SimpleFunc.induction
    (motive := fun f => Measurable (fun (a : α) => ∫⁻ (b : β), f (a, b) ∂κ a)) ?_ ?_ (F n)
  · intro c t ht
    simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    exact measurable_lintegral_indicator_const_of_pointwise_finite κ hκ ht c
  · intro g₁ g₂ _ hm₁ hm₂
    simp only [SimpleFunc.coe_add, Pi.add_apply]
    have h_add :
      (fun a => ∫⁻ b, g₁ (a, b) + g₂ (a, b) ∂κ a) =
        (fun a => ∫⁻ b, g₁ (a, b) ∂κ a) + fun a => ∫⁻ b, g₂ (a, b) ∂κ a := by
      ext1 a
      rw [Pi.add_apply, lintegral_add_left (by fun_prop)]
    rw [h_add]
    exact Measurable.add hm₁ hm₂

/-- The coded LQG measure restricted to the unit disc, as a kernel on canonical profiles (`B_1` of the Palm identity).
Each value is a finite measure (`profileMeasure` is locally finite and `B_1` is bounded). -/
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

/-- **eq:r6-palm of r8 (line 1815), λ-form**: with `λ = Measure.map c P` the law of the canonical profile, for a
nonnegative jointly measurable `Ψ` on canonical profiles times the marked point,
`∫ ∫_{B_1} Ψ(c, z) m_{γ,0}(c)(dz) λ(dc) = ∫_{B_1} ∫ Ψ(Γ_z c, z) λ(dc) d²z`. Derived from `StepM` and
`RawToProfileStep` (PalmStepM.lean) through the Ω-form `palm_omega_of_stepM_stepB`. -/
theorem eq_r6_palm_lambda_of_stepM_stepB {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
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
  exact palm_omega_of_stepM_stepB hG hμ hcJ hM hB Ψ hΨ

end HarmonicBalls

end
