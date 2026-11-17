import HarmonicBalls.Proofs.Potential.LQGClockInsertedAnnealedIncrement

/-! # Summability of annealed inserted annular increments

Positive decay exponents are available in a restricted insertion regime.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set
open scoped NNReal ENNReal
namespace HarmonicBalls

/-- Select integrable occupation and Gaussian truncation exponents with positive decay. -/
theorem exists_annealed_singular_clock_exponents {q γ : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 * (1-q)) :
    ∃ q₂ β d θ : ℝ, q < q₂ ∧ q₂ < 1 ∧ 0 < β ∧ β < 2 ∧ 0 < d ∧
      d < β * (1-q/q₂) ∧ γ < θ ∧ θ < 2*γ ∧
      0 < d-γ^2+(2*γ-θ)^2/2 := by
  obtain ⟨d, hdl, hdu⟩ := exists_between hsub
  have hd0 : 0 < d := lt_of_le_of_lt (by positivity : 0 ≤ γ^2/2) hdl
  have hq1' : 0 < 1-q := by linarith
  have hdb : d / (1-q) < 2 := by
    rw [div_lt_iff₀ hq1']
    linarith
  obtain ⟨β, hβl, hβu⟩ := exists_between hdb
  have hβ0 : 0 < β := lt_trans (div_pos hd0 hq1') hβl
  have hdβ : d < β*(1-q) := (div_lt_iff₀ hq1').mp hβl
  have hβd : 0 < β-d := by nlinarith
  have hr : β*q/(β-d) < 1 := by
    rw [div_lt_iff₀ hβd]
    nlinarith
  obtain ⟨q₂, hq₂l, hq₂u⟩ := exists_between (max_lt hq1 hr)
  have hqq : q < q₂ := lt_of_le_of_lt (le_max_left _ _) hq₂l
  have hq₂0 : 0 < q₂ := hq0.trans hqq
  have hratio : β*q/(β-d) < q₂ := lt_of_le_of_lt (le_max_right _ _) hq₂l
  have hmul : β*q < q₂*(β-d) := (div_lt_iff₀ hβd).mp hratio
  have hd : d < β*(1-q/q₂) := by
    rw [show β*(1-q/q₂) = β - β*q/q₂ by ring]
    apply (lt_sub_iff_add_lt).2
    have hh : β*q/q₂ < β-d := (div_lt_iff₀ hq₂0).2 (by nlinarith)
    linarith
  let e : ℝ := d-γ^2/2
  have he : 0 < e := by dsimp [e]; linarith
  have hv : γ < min (2*γ) (γ + e/(γ+1)) := by
    apply lt_min
    · linarith
    · have : 0 < e/(γ+1) := div_pos he (by linarith)
      linarith
  obtain ⟨θ, hθl, hθu⟩ := exists_between hv
  have hθ2 : θ < 2*γ := hθu.trans_le (min_le_left _ _)
  have hθe : θ-γ < e/(γ+1) := by
    have := hθu.trans_le (min_le_right (2*γ) (γ + e/(γ+1)))
    linarith
  have hmulθ : (θ-γ)*(γ+1) < e := (lt_div_iff₀ (by linarith : 0 < γ+1)).mp hθe
  have hsq : 0 ≤ (θ-γ)^2 := sq_nonneg _
  refine ⟨q₂, β, d, θ, hqq, hq₂u, hβ0, hβu, hd0, hd, hθl, hθ2, ?_⟩
  dsimp [e] at hmulθ
  nlinarith

/-- Annealed absolute increments are summable along dyadic smoothing scales,
uniformly over deterministic outer-radius sequences. -/
theorem summable_inserted_annular_increment_annealed
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq1 : γ*α < 1) (hγ : 0 < γ)
    (hsub : γ^2/2 < 2*(1-γ*α)) (δ : ℕ → ℝ) :
    Summable (fun n : ℕ =>
      let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
      ∫ q, |∫ w, {w : ℂ | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ n ∧ ‖w‖ ≤ 1/2}.indicator (fun w =>
        (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc q.2 (ε/2) w-hcirc q.2 1 0 - α*Real.log (max (ε/2) ‖w‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc q.2 ε w-hcirc q.2 1 0 - α*Real.log (max ε ‖w‖)))) w
        ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
          (volume.restrict (Icc (0 : ℝ) 1))))| ∂((planarBrownianMotion x).prod P)) := by
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
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => abs_nonneg _)) _ hs
  intro n
  have hpos : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
  have hhalf : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1/2 := by
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hb := (inserted_annular_increment_annealed_bound hh x hq0 hqq hq₂ hβ hβ₂ hd0 hd
    hγθ.le hθ.le hpos hhalf (δ n)).2
  dsimp only at hb ⊢
  calc
    _ ≤ ∫ b, A b * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1))*c) +
        B b * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1))*e) ∂(planarBrownianMotion x) := hb
    _ = _ := by rw [integral_add (hAi.mul_const _) (hBi.mul_const _), integral_mul_const, integral_mul_const]

end HarmonicBalls
