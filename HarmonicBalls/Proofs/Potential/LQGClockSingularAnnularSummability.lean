import HarmonicBalls.Proofs.Potential.LQGClockSingularInsertedIncrement
import LatticeProb.LQG.GMCDyadicLimit
import LatticeProb.Gauss.RegressionDualCauchy

/-! # Summable inserted annular increments

Moving annular clock increments have summable field expectations along dyadic scales.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set
open scoped NNReal ENNReal
namespace HarmonicBalls

/-- For almost every Brownian path, moving annular increments have summable field
expectations uniformly over any choice of outer radii. -/
theorem planarBrownianMotion_ae_summable_inserted_moving_annulus_increment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ δ : ℕ → ℝ,
      Summable (fun n : ℕ =>
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        let μ := Measure.map (fun t => b t) ν
        ∫ ω, |∫ w, {w : ℂ | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ n ∧ ‖w‖ ≤ 1/2}.indicator (fun w =>
          (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) w-hcirc ω 1 0 - α*Real.log (max (ε/2) ‖w‖))) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε w-hcirc ω 1 0 - α*Real.log (max ε ‖w‖)))) w ∂μ| ∂P) := by
  obtain ⟨β, θ, hβ0, hβ2, hγθ, hθ, hdecay, hb⟩ :=
    planarBrownianMotion_ae_inserted_moving_annulus_increment_le hh x hq0 hq2 hγ hsub
  filter_upwards [hb] with b hb
  obtain ⟨C, A, hC, hA, hb⟩ := hb
  intro δ
  let c : ℝ := (β*(2-γ*α)/(2+γ*α)-γ^2+(2*γ-θ)^2/2)/2
  let e : ℝ := (θ-γ)^2/2
  let K : ℝ := ((Real.exp (γ^2*Real.log 2)-1)*C+1)/2
  have hc : 0 < c := by dsimp [c]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hs : Summable (fun n : ℕ => K * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * c) +
      2*A*Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * e)) := by
    have h1 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul hc
    have h2 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul he
    exact (summable_nat_add_iff 1).2 ((h1.mul_left K).add (h2.mul_left (2*A)))
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun ω => abs_nonneg _)) _ hs
  intro n
  have hpos : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
  have hhalf : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1/2 := by
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  exact hb (δ n) _ hpos hhalf

/-- For each path, a moving annular increment is integrable in the field. -/
theorem integrable_inserted_moving_annulus_increment_field
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (γ α δ : ℝ) (b : ContinuousPath ℂ) :
    Integrable (fun ω => ∫ w,
      {w : ℂ | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ ∧ ‖w‖ ≤ 1/2}.indicator (fun w =>
        (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) w-hcirc ω 1 0 - α*Real.log (max (ε/2) ‖w‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε w-hcirc ω 1 0 - α*Real.log (max ε ‖w‖)))) w
      ∂(Measure.map (fun t => b t) (Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))))) P := by
  let S : Set ℂ := {w | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ ∧ ‖w‖ ≤ 1/2}
  let f : ℂ → ℝ := fun w => Real.exp (-γ*α*Real.log (max ε ‖w‖))
  let g : ℂ → ℝ := S.indicator f
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const measurable_norm).inter
      ((measurableSet_le measurable_norm measurable_const).inter
        (measurableSet_le measurable_norm measurable_const))
  have hf : Continuous f := Real.continuous_exp.comp (continuous_const.mul
    ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hε).ne')))
  have hgm : Measurable g := hf.measurable.indicator hS
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (1/2 : ℝ)).bddAbove_image hf.continuousOn
  have hgK : ∀ w, |g w| ≤ max K 0 := by
    intro w
    by_cases hw : w ∈ S
    · have hwk : w ∈ Metric.closedBall (0 : ℂ) (1/2 : ℝ) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hw.2.2
      rw [show g w = f w from Set.indicator_of_mem hw _, abs_of_pos (Real.exp_pos _)]
      exact (hK ⟨w, hwk, rfl⟩).trans (le_max_left K 0)
    · rw [show g w = 0 from Set.indicator_of_notMem hw _, abs_zero]
      exact le_max_right K 0
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let μ : Measure ℂ := Measure.map (fun t => b t) ν
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  have hgi : Integrable g μ := by
    apply (integrable_const (max K 0)).mono' hgm.aestronglyMeasurable
    filter_upwards with w
    simpa [Real.norm_eq_abs] using hgK w
  have hgs : ∀ w, g w ≠ 0 → ‖w‖ + ε ≤ 1 := by
    intro w hw
    have hwS : w ∈ S := by
      by_contra hn
      exact hw (Set.indicator_of_notMem hn _)
    linarith [hwS.2.2]
  have hi := hh.integrable_integral_increment hε zero_lt_one μ hgm hgi hgs γ
  refine hi.congr (Filter.Eventually.of_forall fun ω => ?_)
  apply integral_congr_ae
  filter_upwards with w
  by_cases hw : w ∈ S
  · have hhε : ε/2 ≤ ‖w‖ := by linarith [hw.1]
    rw [show S.indicator _ w = _ from Set.indicator_of_mem hw _,
      show g w = _ from Set.indicator_of_mem hw _, max_eq_right hw.1, max_eq_right hhε]
    dsimp [f]
    rw [max_eq_right hw.1]
    have heq (r : ℝ) : γ * (hcirc ω r w - hcirc ω 1 0 - α * Real.log ‖w‖) =
        -γ*α*Real.log ‖w‖ + γ*(hcirc ω r w-hcirc ω 1 0) := by ring
    rw [heq (ε/2), heq ε, Real.exp_add, Real.exp_add]
    ring
  · rw [show S.indicator _ w = _ from Set.indicator_of_notMem hw _,
      show g w = _ from Set.indicator_of_notMem hw _, zero_mul]

/-- For almost every Brownian path and any outer-radius sequence, the moving
annular increments are absolutely summable for almost every field. -/
theorem planarBrownianMotion_ae_field_ae_summable_inserted_moving_annulus_increment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ δ : ℕ → ℝ, ∀ᵐ ω ∂P,
      Summable (fun n : ℕ =>
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        let μ := Measure.map (fun t => b t) ν
        |∫ w, {w : ℂ | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ n ∧ ‖w‖ ≤ 1/2}.indicator (fun w =>
          (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) w-hcirc ω 1 0 - α*Real.log (max (ε/2) ‖w‖))) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε w-hcirc ω 1 0 - α*Real.log (max ε ‖w‖)))) w ∂μ|) := by
  filter_upwards [planarBrownianMotion_ae_summable_inserted_moving_annulus_increment
    hh x hq0 hq2 hγ hsub] with b hb
  intro δ
  apply LatticeProb.Gauss.ae_summable_of_summable_integral _ (fun _ _ => abs_nonneg _) (hb δ)
  intro n
  have hpos : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
  have hhalf : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1/2 := by
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  exact (integrable_inserted_moving_annulus_increment_field hh hpos hhalf γ α (δ n) b).abs

end HarmonicBalls
