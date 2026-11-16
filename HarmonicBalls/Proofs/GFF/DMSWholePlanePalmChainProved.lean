import HarmonicBalls.Proofs.GFF.DMSWholePlaneConsumers
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmMarkedEquality
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmStepMDMS

/-!
# The Palm chain heads for actual whole-plane fields

The Palm chain heads `HarmonicBalls.palm_test_identity`, `HarmonicBalls.lintegral_palm_test`,
`HarmonicBalls.lintegral_palm_open`, `HarmonicBalls.lintegral_palm_borel`, `HarmonicBalls.lintegral_kernel_ball_lt_top`,
`HarmonicBalls.lintegral_palm_psi` and `HarmonicBalls.markedLeft_eq_markedRight` take the unnormalized whole-plane
clause of [DMS, Lemma A.10, p. 184] (`DMSLemmaA10WholePlaneUnnormalized`) as a hypothesis. That clause holds for
every whole-plane GFF `(P, hC, hcirc)` and every `γ`-LQG measure `μ` of it with `γ ∈ (0, 2)` and `α₀ = 0`
(`dmsLemmaA10WholePlaneUnnormalized_holds`). Applying each head to it gives the same statement for such fields
with the range `0 < γ < 2` in place of the clause; no further input is used.

## Main statements

* `HarmonicBalls.IsWholePlaneGFF.palm_test_identity`: the Palm identity for a bounded continuous `ψ` of the
  pairings and a nonnegative continuous `η` supported in the unit disk.
* `HarmonicBalls.IsWholePlaneGFF.lintegral_palm_test`: the same identity in lintegral form.
* `HarmonicBalls.IsWholePlaneGFF.lintegral_palm_open`: the Palm identity for open sets.
* `HarmonicBalls.IsWholePlaneGFF.lintegral_palm_borel`: the Palm identity for Borel sets.
* `HarmonicBalls.IsWholePlaneGFF.lintegral_kernel_ball_lt_top`: the kernel mass of the unit disk is integrable.
* `HarmonicBalls.IsWholePlaneGFF.lintegral_palm_psi`: the Palm identity for measurable functionals.
* `HarmonicBalls.IsWholePlaneGFF.markedLeft_eq_markedRight`: the left and right marked measures agree.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {γ : ℝ}

/-- **Palm test identity for actual whole-plane fields**: for `γ ∈ (0, 2)`, a whole-plane GFF and a `γ`-LQG
measure `μ` of it with `α₀ = 0`, a bounded continuous `ψ` on `ℝ^k`, test functions `φ_j`, and a nonnegative
continuous `η` supported in the open unit disk,
`E[ψ(hC φ) μ_g(η)] = ∫ η(z) E[ψ(hC φ + ∫ dmsShift_z φ)] d²z`. -/
theorem palm_test_identity (hG : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) {η : ℂ → ℝ} (hη : Continuous η)
    (hηs : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z) (htsupp : tsupport η ⊆ Metric.ball (0 : ℂ) 1)
    {k : ℕ} (φ : Fin k → ℂ → ℝ) (hφ : ∀ j, IsTestFunction Set.univ (φ j)) (ψ : (Fin k → ℝ) → ℝ)
    (hψ : Continuous ψ) (C : ℝ) (hψC : ∀ x, |ψ x| ≤ C) :
    ∫ ω, ψ (fun j => hC ω (φ j)) * (∫ z, η z ∂(μ ω)) ∂P =
      ∫ z, η z * ∫ ω, ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) ∂P
        ∂(volume : Measure ℂ) :=
  have := hG.isProbabilityMeasure
  HarmonicBalls.palm_test_identity hG γ hμ (dmsLemmaA10WholePlaneUnnormalized_holds P hγ0 hγ2 hC hcirc μ)
    hη hηs hη0 htsupp φ hφ ψ hψ C hψC

/-- **Palm identity in lintegral form for actual whole-plane fields**: for `γ ∈ (0, 2)`, nonnegative continuous
`ψ` bounded by `C` and a nonnegative continuous `η` supported in the open unit disk. -/
theorem lintegral_palm_test (hG : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) {η : ℂ → ℝ} (hη : Continuous η)
    (hηs : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z) (htsupp : tsupport η ⊆ ball (0 : ℂ) 1) {k : ℕ}
    {φ : Fin k → ℂ → ℝ} (hφ : ∀ j, IsTestFunction Set.univ (φ j)) {ψ : (Fin k → ℝ) → ℝ}
    (hψ : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x) {C : ℝ} (hψC : ∀ x, |ψ x| ≤ C) :
    ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j))) * (∫⁻ z, ENNReal.ofReal (η z) ∂(μ ω)) ∂P =
      ∫⁻ z, ENNReal.ofReal (η z) *
        ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P
        ∂(volume : Measure ℂ) :=
  have := hG.isProbabilityMeasure
  HarmonicBalls.lintegral_palm_test hG γ hμ (dmsLemmaA10WholePlaneUnnormalized_holds P hγ0 hγ2 hC hcirc μ)
    hη hηs hη0 htsupp hφ hψ hψ0 hψC

/-- **Palm identity for open sets for actual whole-plane fields**: for `γ ∈ (0, 2)`, `W` open, `ψ ≥ 0` bounded
continuous on `ℝ^k` and a measurable kernel `κ` almost surely equal to `μ_ω` restricted to the unit disk, the
marked mass of `W ∩ B₁` against `ψ(hC φ)` equals the integral over `W ∩ B₁` of the shifted expectations. -/
theorem lintegral_palm_open (hG : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) {κ : Ω → Measure ℂ} (hκm : Measurable κ)
    (hκa : ∀ᵐ ω ∂P, κ ω = (μ ω).restrict (ball (0 : ℂ) 1)) {W : Set ℂ} (hW : IsOpen W) {k : ℕ}
    {φ : Fin k → ℂ → ℝ} (hφ : ∀ j, IsTestFunction Set.univ (φ j)) {ψ : (Fin k → ℝ) → ℝ}
    (hψ : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x) {C : ℝ} (hψC : ∀ x, |ψ x| ≤ C) :
    ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j))) * κ ω (W ∩ ball (0 : ℂ) 1) ∂P =
      ∫⁻ z in W ∩ ball (0 : ℂ) 1,
        ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P
        ∂(volume : Measure ℂ) :=
  have := hG.isProbabilityMeasure
  HarmonicBalls.lintegral_palm_open hG γ hμ (dmsLemmaA10WholePlaneUnnormalized_holds P hγ0 hγ2 hC hcirc μ)
    hκm hκa hW hφ hψ hψ0 hψC

/-- **Palm identity for Borel sets for actual whole-plane fields**: for `γ ∈ (0, 2)`, `B` Borel, `ψ ≥ 0` bounded
continuous on `ℝ^k` and a measurable kernel `κ` almost surely equal to `μ_ω` restricted to the unit disk, the
marked mass of `B ∩ B₁` against `ψ(hC φ)` equals the integral over `B ∩ B₁` of the shifted expectations. -/
theorem lintegral_palm_borel (hG : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) {κ : Ω → Measure ℂ} (hκm : Measurable κ)
    (hκa : ∀ᵐ ω ∂P, κ ω = (μ ω).restrict (ball (0 : ℂ) 1)) {k : ℕ} {φ : Fin k → ℂ → ℝ}
    (hφ : ∀ j, IsTestFunction Set.univ (φ j)) {ψ : (Fin k → ℝ) → ℝ} (hψ : Continuous ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) {C : ℝ} (hψC : ∀ x, |ψ x| ≤ C) {B : Set ℂ} (hB : MeasurableSet B) :
    ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j))) * κ ω (B ∩ ball (0 : ℂ) 1) ∂P =
      ∫⁻ z in B ∩ ball (0 : ℂ) 1,
        ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P
        ∂(volume : Measure ℂ) :=
  have := hG.isProbabilityMeasure
  HarmonicBalls.lintegral_palm_borel hG γ hμ (dmsLemmaA10WholePlaneUnnormalized_holds P hγ0 hγ2 hC hcirc μ)
    hκm hκa hφ hψ hψ0 hψC hB

/-- **Finite kernel mass for actual whole-plane fields**: for `γ ∈ (0, 2)` and a measurable kernel `κ` almost
surely equal to `μ_ω` restricted to the unit disk, `∫⁻ κ_ω(B₁) dP < ∞`. -/
theorem lintegral_kernel_ball_lt_top (hG : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) {κ : Ω → Measure ℂ} (hκm : Measurable κ)
    (hκa : ∀ᵐ ω ∂P, κ ω = (μ ω).restrict (ball (0 : ℂ) 1)) {k : ℕ} {φ : Fin k → ℂ → ℝ}
    (hφ : ∀ j, IsTestFunction Set.univ (φ j)) :
    ∫⁻ ω, κ ω (Set.univ ∩ ball (0 : ℂ) 1) ∂P < ⊤ :=
  have := hG.isProbabilityMeasure
  HarmonicBalls.lintegral_kernel_ball_lt_top hG γ hμ (dmsLemmaA10WholePlaneUnnormalized_holds P hγ0 hγ2 hC hcirc μ)
    hκm hκa hφ

/-- **Palm identity for measurable functionals for actual whole-plane fields**: for `γ ∈ (0, 2)`, a measurable
`Ψ : (Fin k → ℝ) → ℝ≥0∞`, a Borel set `B` and a measurable kernel `κ` almost surely equal to `μ_ω` restricted to
the unit disk, the marked integral of `Ψ(hC φ)` against `κ_ω(B ∩ B₁)` equals the integral over `B ∩ B₁` of the
shifted expectations of `Ψ`. -/
theorem lintegral_palm_psi (hG : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) {κ : Ω → Measure ℂ} (hκm : Measurable κ)
    (hκa : ∀ᵐ ω ∂P, κ ω = (μ ω).restrict (ball (0 : ℂ) 1)) {k : ℕ} {φ : Fin k → ℂ → ℝ}
    (hφ : ∀ j, IsTestFunction Set.univ (φ j)) {B : Set ℂ} (hB : MeasurableSet B)
    {Ψ : (Fin k → ℝ) → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ ω, Ψ (fun j => hC ω (φ j)) * κ ω (B ∩ ball (0 : ℂ) 1) ∂P =
      ∫⁻ z in B ∩ ball (0 : ℂ) 1,
        ∫⁻ ω, Ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) ∂P ∂(volume : Measure ℂ) :=
  have := hG.isProbabilityMeasure
  HarmonicBalls.lintegral_palm_psi hG γ hμ (dmsLemmaA10WholePlaneUnnormalized_holds P hγ0 hγ2 hC hcirc μ)
    hκm hκa hφ hB hΨ

/-- **Marked left equals marked right for actual whole-plane fields**: for `γ ∈ (0, 2)` and a random kernel `κ`
equal to `μ|_{B₁}` almost surely, with measurable sections, the left marked measure (`markedLeft`) equals the
right one (`markedRight`). -/
theorem markedLeft_eq_markedRight (hG : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) {κ : Ω → Measure ℂ} (hκm : Measurable κ)
    (hκa : ∀ᵐ ω ∂P, κ ω = (μ ω).restrict (ball (0 : ℂ) 1))
    (hκs : ∀ S : Set (PairFun × ℂ), MeasurableSet[MeasurableSpace.prod inferInstance inferInstance] S →
      Measurable fun ω => κ ω {z | (toPairFun (hC ω), z) ∈ S}) :
    markedLeft P hC κ = markedRight P γ hC :=
  have := hG.isProbabilityMeasure
  HarmonicBalls.markedLeft_eq_markedRight hG γ hμ (dmsLemmaA10WholePlaneUnnormalized_holds P hγ0 hγ2 hC hcirc μ)
    hκm hκa hκs

end IsWholePlaneGFF

end HarmonicBalls
