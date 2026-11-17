import HarmonicBalls.Proofs.Potential.LQGClockInsertedAnnealedSummability

/-! # Uniform annular increment bounds

One summable sequence controls the expected inserted clock increments uniformly
in the outer radius.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set
open scoped NNReal ENNReal
namespace HarmonicBalls

/-- Expected annular increments admit a summable bound independent of the outer radius. -/
theorem exists_summable_uniform_inserted_annular_increment_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq1 : γ*α < 1) (hγ : 0 < γ)
    (hsub : γ^2/2 < 2*(1-γ*α)) :
    ∃ B : ℕ → ℝ, Summable B ∧ ∀ (n : ℕ) (δ : ℝ),
      let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
      ∫ q, |∫ w, {w : ℂ | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ ∧ ‖w‖ ≤ 1/2}.indicator (fun w =>
        (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc q.2 (ε/2) w-hcirc q.2 1 0 - α*Real.log (max (ε/2) ‖w‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc q.2 ε w-hcirc q.2 1 0 - α*Real.log (max ε ‖w‖)))) w
        ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
          (volume.restrict (Icc (0 : ℝ) 1))))| ∂((planarBrownianMotion x).prod P) ≤ B n := by
  obtain ⟨q₂, β, d, θ, hqq, hq₂, hβ, hβ₂, hd0, hd, hγθ, hθ, hdecay⟩ :=
    exists_annealed_singular_clock_exponents hq0 hq1 hγ hsub
  let A : ContinuousPath ℂ → ℝ := fun b =>
    ((Real.exp (γ^2*Real.log 2)-1)*(2^d * unitSingularPairAllRadiusEnvelope 0 (γ*α) d b)+1)/2
  let B : ContinuousPath ℂ → ℝ := fun b => 2*unitSingularOccupationEnvelope 0 (γ*α) b
  have hAi : Integrable A (planarBrownianMotion x) := by
    have hp := integrable_unitSingularPairAllRadiusEnvelope x 0 hq0 hqq hq₂ hβ hβ₂ hd
    exact ((hp.const_mul _).const_mul _ |>.add (integrable_const 1)).div_const 2
  have hBi : Integrable B (planarBrownianMotion x) := by
    exact (integrable_unitSingularOccupationEnvelope x 0 hq0 (by linarith)).const_mul 2
  let c : ℝ := (d-γ^2+(2*γ-θ)^2/2)/2
  let e : ℝ := (θ-γ)^2/2
  have hc : 0 < c := by dsimp [c]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hs : Summable (fun n : ℕ =>
      (∫ b, A b ∂(planarBrownianMotion x)) * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1))*c) +
      (∫ b, B b ∂(planarBrownianMotion x)) * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1))*e)) := by
    have h1 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul hc
    have h2 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul he
    exact (summable_nat_add_iff 1).2 ((h1.mul_left _).add (h2.mul_left _))
  refine ⟨_, hs, ?_⟩
  intro n δ
  have hpos : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
  have hhalf : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1/2 := by
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hb := (inserted_annular_increment_annealed_bound hh x hq0 hqq hq₂ hβ hβ₂ hd0 hd
    hγθ.le hθ.le hpos hhalf δ).2
  dsimp only at hb ⊢
  calc
    _ ≤ ∫ b, A b * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1))*c) +
        B b * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1))*e) ∂(planarBrownianMotion x) := hb
    _ = _ := by rw [integral_add (hAi.mul_const _) (hBi.mul_const _), integral_mul_const, integral_mul_const]


end HarmonicBalls
