import HarmonicBalls.Proofs.Potential.LQGClockSingularIncrement

/-! # Inserted clock increments near the insertion

A moving annular cutoff admits a common pathwise field-increment estimate.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set
open scoped NNReal ENNReal
namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Inserted clock increments outside the smoothing radius have a common
pathwise bound, uniformly over the outer cutoff and smoothing scale. -/
theorem planarBrownianMotion_ae_inserted_moving_annulus_increment_le
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) :
    ∃ β θ : ℝ, 0 < β ∧ β < 2 ∧ γ < θ ∧ θ < 2*γ ∧
      0 < β*(2-γ*α)/(2+γ*α) - γ^2 + (2*γ-θ)^2/2 ∧
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ᵐ b ∂(planarBrownianMotion x), ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
        ∀ δ ε : ℝ, 0 < ε → ε ≤ 1/2 →
        let μ := Measure.map (fun t => b t) ν
        (∫ ω, |∫ w, {w : ℂ | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ ∧ ‖w‖ ≤ 1/2}.indicator (fun w =>
          (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) w-hcirc ω 1 0 - α*Real.log (max (ε/2) ‖w‖))) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε w-hcirc ω 1 0 - α*Real.log (max ε ‖w‖)))) w ∂μ| ∂P) ≤
        ((Real.exp (γ^2*Real.log 2)-1)*C+1)/2 *
          Real.exp (Real.log ε * ((β*(2-γ*α)/(2+γ*α)-γ^2+(2*γ-θ)^2/2)/2)) +
        2*A*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨β, θ, hβ0, hβ2, hγθ, hθ, hdecay, hb⟩ :=
    planarBrownianMotion_ae_singular_field_increment_le hh x 0 hq0 hq2 hγ hsub
  refine ⟨β, θ, hβ0, hβ2, hγθ, hθ, hdecay, ?_⟩
  filter_upwards [hb] with b hb
  obtain ⟨C, A, hC, hA, hb⟩ := hb
  refine ⟨C, A, hC, hA, ?_⟩
  intro δ ε hε hεhalf
  let S : Set ℂ := {w | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ ∧ ‖w‖ ≤ 1/2}
  let g : ℂ → ℝ := S.indicator (fun w => Real.exp (-γ*α*Real.log (max ε ‖w‖)))
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const measurable_norm).inter
      ((measurableSet_le measurable_norm measurable_const).inter
        (measurableSet_le measurable_norm measurable_const))
  have hgm : Measurable g := by
    apply Measurable.indicator _ hS
    exact (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hε).ne')))).measurable
  have hgM : ∀ w, ENNReal.ofReal |g w| ≤ ENNReal.ofReal 1 *
      (ENNReal.ofReal ‖w-(0 : ℂ)‖)^(-(γ*α)) := by
    intro w
    by_cases hw : w ∈ S
    · have hw0 : 0 < ‖w‖ := hε.trans_le hw.1
      rw [show g w = _ from Set.indicator_of_mem hw _, max_eq_right hw.1,
        abs_of_pos (Real.exp_pos _), sub_zero, ENNReal.ofReal_one, one_mul]
      rw [ENNReal.ofReal_rpow_of_pos hw0, Real.rpow_def_of_pos hw0]
      apply le_of_eq
      congr 2
      ring
    · rw [show g w = _ from Set.indicator_of_notMem hw _, abs_zero, ENNReal.ofReal_zero]
      exact zero_le
  have hgs : ∀ w, g w ≠ 0 → ‖w‖ ≤ 1/2 := by
    intro w hw
    by_contra h
    have hn : w ∉ S := fun hwS => h hwS.2.2
    exact hw (Set.indicator_of_notMem hn _)
  have hbound := hb g hgm 1 (by norm_num) hgM hgs ε hε hεhalf
  simp only [one_pow, one_mul, mul_one] at hbound
  refine (le_of_eq ?_).trans hbound
  congr 1
  funext ω
  congr 1
  apply integral_congr_ae
  filter_upwards with w
  by_cases hw : w ∈ S
  · have hhε : ε/2 ≤ ‖w‖ := by linarith [hw.1]
    rw [show S.indicator _ w = _ from Set.indicator_of_mem hw _,
      show g w = _ from Set.indicator_of_mem hw _, max_eq_right hw.1, max_eq_right hhε]
    have heq (r : ℝ) : γ * (hcirc ω r w - hcirc ω 1 0 - α * Real.log ‖w‖) =
        -γ*α*Real.log ‖w‖ + γ*(hcirc ω r w-hcirc ω 1 0) := by ring
    rw [heq (ε/2), heq ε, Real.exp_add, Real.exp_add]
    ring
  · rw [show S.indicator _ w = _ from Set.indicator_of_notMem hw _,
      show g w = _ from Set.indicator_of_notMem hw _, zero_mul]

end HarmonicBalls
