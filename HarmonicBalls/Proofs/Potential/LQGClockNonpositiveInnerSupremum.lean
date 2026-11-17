import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveInsertionCutoff
import LatticeProb.Gauss.RegressionDualCauchy

/-! # Summable inner clock increments

A single summable envelope controls inner-ball field increments for almost every Brownian path.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- At a fixed start, one summable sequence bounds the field expectations of all
zero-insertion inner-ball increments and all unit-time occupation submeasures. -/
theorem planarBrownianMotion_ae_summable_inner_increment_envelope
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∃ R : ℕ → ℝ,
      Summable R ∧ (∀ n, 0 ≤ R n) ∧
      ∀ δ : ℝ, δ ≤ 1/2 → ∀ μ : Measure ℂ,
      μ ≤ Measure.map (fun t => b t) ν → ∀ n : ℕ,
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        (∫ ω, |∫ z, ({z : ℂ | ‖z‖ < δ}.indicator (fun _ => (1 : ℝ)) z) *
          ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0)) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0))) ∂μ| ∂P) ≤ R n := by
  obtain ⟨θ, d, hγθ, hθ, hd0, hd2, hp, hb⟩ :=
    ae_brownian_inner_ball_increment_le_riesz_energy hh hγ0 hγ2 x
  filter_upwards [hb] with b hb
  let u : ℝ := (d-γ^2+(2*γ-θ)^2/2)/2
  let v : ℝ := (θ-γ)^2/2
  let A : ℝ := ((Real.exp (γ^2*Real.log 2)-1)*(unitOccupationRieszEnergy d b * 2^d)+1)/2
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    have he : 0 ≤ Real.exp (γ^2*Real.log 2)-1 :=
      sub_nonneg.mpr (Real.one_le_exp (by positivity))
    have hE : 0 ≤ unitOccupationRieszEnergy d b := ENNReal.toReal_nonneg
    positivity
  let R : ℕ → ℝ := fun n => A * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * u) +
    2 * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * v)
  refine ⟨R, ?_, ?_, ?_⟩
  · have h1 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul hu
    have h2 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul hv
    exact (summable_nat_add_iff 1).2 ((h1.mul_left A).add (h2.mul_left 2))
  · intro n
    dsimp [R]
    positivity
  · intro δ hδ μ hμ n
    have hpos : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
    have hhalf : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1/2 := by
      rw [pow_succ]
      have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    exact hb δ hδ μ hμ _ hpos hhalf

/-- Along arbitrary inner radii and occupation submeasures, the zero-insertion
dyadic field-expectation increments are summable on one Brownian event. -/
theorem planarBrownianMotion_ae_summable_inner_increment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ δ : ℕ → ℝ, (∀ n, δ n ≤ 1/2) →
      ∀ μ : ℕ → Measure ℂ, (∀ n, μ n ≤ Measure.map (fun t => b t) ν) →
      Summable (fun n : ℕ =>
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        ∫ ω, |∫ z, ({z : ℂ | ‖z‖ < δ n}.indicator (fun _ => (1 : ℝ)) z) *
          ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0)) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0))) ∂(μ n)| ∂P) := by
  filter_upwards [planarBrownianMotion_ae_summable_inner_increment_envelope hh hγ0 hγ2 x] with b hb
  obtain ⟨R, hR, _, hbound⟩ := hb
  intro δ hδ μ hμ
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun ω => abs_nonneg _)) _ hR
  intro n
  exact hbound (δ n) (hδ n) (μ n) (hμ n) n

end HarmonicBalls
