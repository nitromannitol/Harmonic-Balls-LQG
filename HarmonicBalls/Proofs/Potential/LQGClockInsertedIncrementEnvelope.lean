import HarmonicBalls.Proofs.Potential.LQGClockSingularWeightIncrement
import HarmonicBalls.Proofs.Potential.LQGClockSingularInsertedIncrement

/-! # Integrable envelopes for inserted clock increments

Moving annular increments are controlled by integrable Brownian occupation envelopes.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set
open scoped NNReal ENNReal
namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- A moving annular inserted increment has a common bound in terms of integrable
Brownian occupation envelopes. -/
theorem ae_inserted_moving_annulus_integrable_envelope
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ α q₂ β d θ : ℝ} (hq : 0 < γ*α) (hqq : γ*α < q₂) (hq₂ : q₂ < 1)
    (hβ : 0 < β) (hβ₂ : β < 2) (hd0 : 0 < d)
    (hd : d < β * (1 - (γ*α)/q₂)) (hγθ : γ ≤ θ) (hθ : θ ≤ 2*γ) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ δ ε : ℝ, 0 < ε → ε ≤ 1/2 →
      let μ := Measure.map (fun t => b t) ν
      (∫ ω, |∫ w, {w : ℂ | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ ∧ ‖w‖ ≤ 1/2}.indicator (fun w =>
        (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) w-hcirc ω 1 0 - α*Real.log (max (ε/2) ‖w‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε w-hcirc ω 1 0 - α*Real.log (max ε ‖w‖)))) w ∂μ| ∂P) ≤
      ((Real.exp (γ^2*Real.log 2)-1)*(2^d * unitSingularPairAllRadiusEnvelope 0 (γ*α) d b)+1)/2 *
        Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
      2*unitSingularOccupationEnvelope 0 (γ*α) b * Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  filter_upwards [ae_brownian_singular_submeasure_field_increment_le hh x 0 hq hqq hq₂ hβ hβ₂ hd0 hd] with b hb
  intro δ ε hε hεhalf
  let μ := Measure.map (fun t => b t) ν
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
  have hgM : ∀ w, ENNReal.ofReal |g w| ≤
      (ENNReal.ofReal ‖w-(0 : ℂ)‖)^(-(γ*α)) := by
    intro w
    by_cases hw : w ∈ S
    · have hw0 : 0 < ‖w‖ := hε.trans_le hw.1
      rw [show g w = _ from Set.indicator_of_mem hw _, max_eq_right hw.1,
        abs_of_pos (Real.exp_pos _), sub_zero]
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
  have hgs1 : ∀ w, g w ≠ 0 → ‖w‖ ≤ 1 - 1/2 := by
    simpa only [show (1 : ℝ) - 1/2 = 1/2 by norm_num] using hgs
  have hbound := hb g hgm hgM μ le_rfl (R := 1) zero_lt_one hγθ hθ hgs1 ε hε hεhalf
  simp only [Real.log_one, zero_mul, Real.exp_zero, mul_one] at hbound
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



/-- The right-hand side of the moving-annulus bound is Brownian integrable. -/
theorem integrable_inserted_increment_envelope (x : ℂ)
    {γ α q₂ β d θ : ℝ} (hq : 0 < γ*α) (hqq : γ*α < q₂) (hq₂ : q₂ < 1)
    (hβ : 0 < β) (hβ₂ : β < 2) (hd : d < β * (1 - (γ*α)/q₂)) (ε : ℝ) :
    Integrable (fun b =>
      ((Real.exp (γ^2*Real.log 2)-1)*(2^d * unitSingularPairAllRadiusEnvelope 0 (γ*α) d b)+1)/2 *
        Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
      2*unitSingularOccupationEnvelope 0 (γ*α) b * Real.exp (Real.log ε * ((θ-γ)^2/2)))
      (planarBrownianMotion x) := by
  have hp := integrable_unitSingularPairAllRadiusEnvelope x 0 hq hqq hq₂ hβ hβ₂ hd
  have ho := integrable_unitSingularOccupationEnvelope x 0 hq (by linarith)
  exact (((hp.const_mul _).const_mul _).add (integrable_const 1) |>.div_const 2 |>.mul_const _).add
    ((ho.const_mul 2).mul_const _)

end HarmonicBalls
