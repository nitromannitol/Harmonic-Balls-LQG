import HarmonicBalls.Proofs.Potential.LQGClockAnnularUniformIntegrability
import HarmonicBalls.Proofs.Potential.BrownianExpectedExitGreen
import MarkovProcess.Trajectory.ExitTimeExponentialMoment

/-! # Annular clock integrability at Brownian exit

Continuous densities restricted to a compact annulus have integrable occupation
up to the exit time of a bounded open domain.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Filter Set HarmonicBalls.Section6
open scoped NNReal ENNReal Topology ZeroAtInfty

namespace HarmonicBalls

/-- The annular occupation of a continuous density up to Brownian exit is integrable. -/
theorem integrable_annular_clock_exit_of_continuous {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (x : ℂ) (f : ℂ → ℝ) (hf : Continuous f) (δ : ℝ) :
    Integrable (fun b : ContinuousPath ℂ => ∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal))
      (planarBrownianMotion x) := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let g : ℂ → ℝ := A.indicator f
  have hg : Measurable g := hf.measurable.indicator hA
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (1/2 : ℝ)).bddAbove_image hf.norm.continuousOn
  have hgK : ∀ z, ‖g z‖ ≤ max K 0 := by
    intro z
    by_cases hz : z ∈ A
    · have hzk : z ∈ Metric.closedBall (0 : ℂ) (1/2 : ℝ) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
      rw [show g z = f z from Set.indicator_of_mem hz _]
      exact (hK ⟨z, hzk, rfl⟩).trans (le_max_left K 0)
    · rw [show g z = 0 from Set.indicator_of_notMem hz _, norm_zero]
      exact le_max_right K 0
  let τ : ContinuousPath ℂ → ℝ := fun b => (ContinuousPath.exitTime D b).toReal
  have hτ : Measurable τ := ENNReal.measurable_toReal.comp (ContinuousPath.measurable_exitTime D hD)
  have hτint : Integrable τ (planarBrownianMotion x) :=
    GreenOccupation.integrable_exitTime_toReal hD hDb x
  have heval : Measurable (fun p : ContinuousPath ℂ × ℝ => p.1 p.2.toNNReal) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hF : Measurable (fun p : ContinuousPath ℂ × ℝ => g (p.1 p.2.toNNReal)) := hg.comp heval
  let S : Set (ContinuousPath ℂ × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ τ p.1}
  have hS : MeasurableSet S := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (hτ.comp measurable_fst))
  have hI : StronglyMeasurable (fun b : ContinuousPath ℂ =>
      ∫ s in (0 : ℝ)..τ b, g (b s.toNNReal)) := by
    have h := (hF.indicator hS).stronglyMeasurable.integral_prod_right' (ν := volume)
    convert h using 1
    funext b
    rw [intervalIntegral.integral_of_le ENNReal.toReal_nonneg]
    change (∫ s in Set.Ioc 0 (τ b), g (b s.toNNReal)) = _
    rw [← integral_indicator measurableSet_Ioc]
    rfl
  refine (hτint.const_mul (max K 0)).mono' hI.aestronglyMeasurable
    (Filter.Eventually.of_forall ?_)
  intro b
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := τ b) (fun s _ => hgK (b s.toNNReal))
  simpa [τ, g, A, abs_of_nonneg ENNReal.toReal_nonneg, le_max_right K 0] using hbound

/-- Each dyadic annular clock is integrable up to the actual Brownian exit,
for almost every field and a fixed Brownian starting point. -/
theorem ae_integrable_annular_clock_exit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    (γ α δ : ℝ) (x : ℂ) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, Integrable (fun b : ContinuousPath ℂ =>
      ∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (dyadicScale k)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z))
          (b s.toNNReal)) (planarBrownianMotion x) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  filter_upwards [hcont, ae_recentered_inserted_circle_average hh α] with ω hcont hrec
  intro k
  have hr := dyadicScale_pos k
  have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) =
      fun z => hcirc ω (dyadicScale k) z - hcirc ω 1 0 -
        α * Real.log (max (dyadicScale k) ‖z‖) := by
    funext z
    exact (hrec _ z hr).symm
  have hc : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) := by
    rw [heq]
    exact ((hcont _ hr).sub continuous_const).sub
      (continuous_const.mul ((continuous_const.max continuous_norm).log
        (fun _ => (lt_max_of_lt_left hr).ne')))
  exact integrable_annular_clock_exit_of_continuous hD hDb x _
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc))) δ

/-- The expected Brownian exit time is uniformly bounded over the starting point. -/
theorem exists_uniform_planarBrownianMotion_exitTime_mean_le {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) :
    ∃ M : ℝ≥0, ∀ x : ℂ,
      (∫⁻ b, ContinuousPath.exitTime D b ∂planarBrownianMotion x) ≤ (M : ℝ≥0∞) := by
  obtain ⟨g, hg, hgc, hΔ⟩ := GreenOccupation.exists_contDiff_hasCompactSupport_laplacian_eq_neg_two hDb
  obtain ⟨f, hfg, hgen⟩ := exists_planarBrownian_generator_eq_half_laplacian g hg hgc
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0)
  have hLf : ∀ y ∈ D,
      (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) y ≤ -1 := by
    intro y hy
    rw [hgen y, hΔ y hy]
    norm_num
  have hm : ∀ y, -M ≤ (f : C₀(ℂ, ℝ)) y := by
    intro y
    rw [hfg y]
    exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using hM y)).1
  refine ⟨Real.toNNReal (2 * M), ?_⟩
  intro x
  rw [planarBrownianMotion_eq_continuousProcess]
  refine le_trans (isFellerKernelSemigroup_planarHeatSemigroup.lintegral_exitTime_le
    isConservative_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup f D hD hLf hm x) ?_
  have hi : (f : C₀(ℂ, ℝ)) x - -M ≤ 2 * M := by
    have hx := (abs_le.mp (by simpa only [Real.norm_eq_abs] using hM x)).2
    rw [hfg x]
    linarith
  simpa [ENNReal.coe_nnreal_eq, Real.toNNReal_of_nonneg (show 0 ≤ 2 * M from mul_nonneg (by norm_num) hM0)] using
    ENNReal.ofReal_le_ofReal hi

/-- The exponential moments of Brownian exit times are uniformly bounded over starting points. -/
theorem exists_uniform_planarBrownianMotion_exitTime_exponential_moment {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x : ℂ,
      (∫⁻ b, ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime D) b
        ∂planarBrownianMotion x) ≤ C := by
  obtain ⟨M, hM⟩ := exists_uniform_planarBrownianMotion_exitTime_mean_le hD hDb
  let lam : ℝ := Real.log 2 / (4 * ((M : ℝ) + 1))
  have hl : 0 < lam := by dsimp [lam]; positivity
  have hrate : Real.exp (lam * (2 * (M : ℝ))) < 2 := by
    calc
      Real.exp (lam * (2 * (M : ℝ))) < Real.exp (Real.log 2) := ?_
      _ = 2 := Real.exp_log (by norm_num)
    apply Real.exp_lt_exp.mpr
    dsimp [lam]
    have hM0 : 0 ≤ (M : ℝ) := M.coe_nonneg
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hd : 0 < 4 * ((M : ℝ) + 1) := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
    have hsmall : 2 * (M : ℝ) < 4 * ((M : ℝ) + 1) := by linarith
    nlinarith [mul_lt_mul_of_pos_left hsmall hlog]
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (lam * (2 * (M : ℝ)))) *
    (1 - 2⁻¹ * ENNReal.ofReal (Real.exp (lam * (2 * (M : ℝ)))))⁻¹
  refine ⟨lam, hl, C, ?_, ?_⟩
  · dsimp [C]
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    apply ENNReal.inv_lt_top.mpr
    apply tsub_pos_of_lt
    have he : ENNReal.ofReal (Real.exp (lam * (2 * (M : ℝ)))) < 2 := by
      simpa using (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < 2)).2 hrate
    have : (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (Real.exp (lam * (2 * (M : ℝ)))) < 1 := by
      have hh := ENNReal.mul_lt_mul_left (show (2 : ℝ≥0∞)⁻¹ ≠ 0 by simp)
        (show (2 : ℝ≥0∞)⁻¹ ≠ ⊤ by simp) he
      rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)] at hh
      simpa only [mul_comm] using hh
    exact this

  · intro x
    rw [planarBrownianMotion_eq_continuousProcess]
    exact isConservative_planarHeatSemigroup.lintegral_exponentialStoppingWeight_exitTime_le_of_lintegral_le
      _ isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup
      D hD M (by intro y; simpa only [← planarBrownianMotion_eq_continuousProcess] using hM y)
      lam hl.le hrate x

/-- A bounded open domain has a positive Brownian exit-time exponential moment,
with a rate independent of the starting point. -/
theorem exists_planarBrownianMotion_exitTime_exponential_moment {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x : ℂ,
      (∫⁻ b, ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime D) b
        ∂planarBrownianMotion x) < ⊤ := by
  obtain ⟨lam, hlam, C, hC, hbound⟩ :=
    exists_uniform_planarBrownianMotion_exitTime_exponential_moment hD hDb
  exact ⟨lam, hlam, fun x => (hbound x).trans_lt hC⟩

end HarmonicBalls
