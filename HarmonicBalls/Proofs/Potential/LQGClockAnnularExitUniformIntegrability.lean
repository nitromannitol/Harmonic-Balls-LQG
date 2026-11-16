import HarmonicBalls.Proofs.Potential.LQGClockAnnularUniformIntegrability
import HarmonicBalls.Proofs.Potential.BrownianExpectedExitGreen
import MarkovProcess.Trajectory.ExitTimeExponentialMoment
import LatticeProb.LQG.LQGCircleMoments

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

private theorem real_excess_le_exp (lam t T : ℝ) (hlam : 0 < lam) :
    max (t - T) 0 ≤ (lam⁻¹ * Real.exp (-lam * T)) * Real.exp (lam * t) := by
  have hle : lam * (t - T) ≤ Real.exp (lam * (t - T)) := by
    linarith [Real.add_one_le_exp (lam * (t - T))]
  have heq : Real.exp (lam * (t - T)) = Real.exp (-lam * T) * Real.exp (lam * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hle
  apply max_le
  · have h : t - T ≤ (Real.exp (-lam * T) * Real.exp (lam * t)) / lam :=
      (le_div_iff₀ hlam).2 (by simpa [mul_comm] using hle)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  · positivity

/-- Expected exit-time excess decays exponentially, uniformly over starting points. -/
theorem exists_uniform_planarBrownianMotion_exitTime_excess_le_exp {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x : ℂ, ∀ T : ℝ, 0 ≤ T →
      (∫⁻ b, ContinuousPath.exitTime D b - ENNReal.ofReal T ∂planarBrownianMotion x) ≤
        ENNReal.ofReal (lam⁻¹ * Real.exp (-lam * T)) * C := by
  obtain ⟨lam, hlam, C, hC, hbound⟩ :=
    exists_uniform_planarBrownianMotion_exitTime_exponential_moment hD hDb
  refine ⟨lam, hlam, C, hC, ?_⟩
  intro x T hT
  have ht := ContinuousPath.ae_lt_top_of_lintegral_exponentialStoppingWeight_ne_top lam
    (ContinuousPath.measurable_exitTime D hD) ((hbound x).trans_lt hC).ne
  calc
    (∫⁻ b, ContinuousPath.exitTime D b - ENNReal.ofReal T ∂planarBrownianMotion x) ≤
        ∫⁻ b, ENNReal.ofReal (lam⁻¹ * Real.exp (-lam * T)) *
          ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime D) b
          ∂planarBrownianMotion x := by
      apply lintegral_mono_ae
      filter_upwards [ht] with b hb
      rw [ContinuousPath.exponentialStoppingWeight_of_ne_top lam _ hb.ne,
        ← ENNReal.ofReal_mul (by positivity)]
      nth_rewrite 1 [← ENNReal.ofReal_toReal hb.ne]
      rw [← ENNReal.ofReal_sub _ hT]
      exact ENNReal.ofReal_le_ofReal ((max_le_iff.mp (real_excess_le_exp lam
        (ContinuousPath.exitTime D b).toReal T hlam)).1)
    _ = ENNReal.ofReal (lam⁻¹ * Real.exp (-lam * T)) *
        (∫⁻ b, ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime D) b
          ∂planarBrownianMotion x) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := by gcongr; exact hbound x

/-- The first moment of the normalized inserted density is its insertion weight. -/
theorem integral_inserted_clock_density_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (γ α : ℝ) {z : ℂ} (hz : ‖z‖ + ε ≤ 1) :
    (∫ ω, ε ^ (γ ^ 2 / 2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z) ∂P) =
      Real.exp (-(γ * α) * Real.log (max ε ‖z‖)) := by
  let A := Real.exp (-(γ * α) * Real.log (max ε ‖z‖))
  have heq : (∫ ω, ε ^ (γ ^ 2 / 2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z) ∂P) =
      A * ∫ ω, ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z) ∂P := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_recentered_inserted_circle_average hh α, hh.ae_circleAverage_one_zero] with ω hω hzero
    rw [← hω ε z hε, hzero]
    simp only [sub_zero]
    have hz' : γ * (hcirc ω ε z - α * Real.log (max ε ‖z‖)) =
        γ * hcirc ω ε z + (-(γ * α) * Real.log (max ε ‖z‖)) := by ring
    rw [hz', Real.exp_add]
    dsimp [A]
    ring
  rw [heq, hh.integral_rpow_mul_exp_circle hε hz γ, mul_one]

/-- The inserted circle-average density is integrable at a positive scale. -/
theorem integrable_inserted_clock_density {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (γ α : ℝ) (z : ℂ) :
    Integrable (fun ω => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) P := by
  let A := Real.exp (-(γ * α) * Real.log (max ε ‖z‖))
  have h : Integrable (fun ω => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z)) P := by
    have hi := hh.integrable_exp_sum_circle hε (fun _ : Fin 1 => z) (fun _ => γ)
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at hi
    exact hi.const_mul _
  apply (h.const_mul A).congr
  filter_upwards [ae_recentered_inserted_circle_average hh α, hh.ae_circleAverage_one_zero] with ω hω hzero
  rw [← hω ε z hε, hzero]
  simp only [sub_zero]
  have hz' : γ * (hcirc ω ε z - α * Real.log (max ε ‖z‖)) =
      γ * hcirc ω ε z + (-(γ * α) * Real.log (max ε ‖z‖)) := by ring
  rw [hz', Real.exp_add]
  dsimp [A]
  ring

/-- The extended first moment of the inserted density equals its insertion weight. -/
theorem lintegral_inserted_clock_density_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (γ α : ℝ) {z : ℂ} (hz : ‖z‖ + ε ≤ 1) :
    (∫⁻ ω, ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) ∂P) =
      ENNReal.ofReal (Real.exp (-(γ * α) * Real.log (max ε ‖z‖))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_inserted_clock_density hh hε γ α z)]
  · rw [integral_inserted_clock_density_eq hh hε γ α hz]
  · filter_upwards with ω
    positivity

/-- Field-averaged annular occupation equals the insertion-weighted spatial measure. -/
theorem lintegral_annular_inserted_density_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε δ : ℝ}
    (hε : 0 < ε) (hεδ : ε ≤ δ) (hεhalf : ε ≤ 1/2)
    (γ α : ℝ) (ν : Measure ℂ) [SFinite ν] :
    (∫⁻ ω, ∫⁻ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator
      (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) z ∂ν ∂P) =
    ∫⁻ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator
      (fun z => ENNReal.ofReal (Real.exp (-(γ * α) * Real.log ‖z‖))) z ∂ν := by
  have := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let F : Ω × ℂ → ℝ≥0∞ := fun q => A.indicator (fun z =>
    ENNReal.ofReal (ε ^ (γ^2/2) * Real.exp (γ*(H q.1 ε z - H q.1 1 0 -
      α*Real.log (max ε ‖z‖))))) q.2
  have h1 : Measurable (fun q : Ω × ℂ => H q.1 ε q.2) :=
    (hHm ε hε).comp measurable_swap
  have h2 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
    (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
  have hF : Measurable F := by
    apply Measurable.indicator _ (hA.preimage measurable_snd)
    exact (measurable_const.mul (measurable_const.mul ((h1.sub h2).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp).ennreal_ofReal
  have heq : ∀ᵐ ω ∂P, ∀ z, F (ω,z) = A.indicator (fun z =>
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) z := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec z
    dsimp [F]
    simp only [Set.indicator_apply]
    split_ifs with hz
    · rw [hω ε z, hω 1 0, hrec ε z hε]
    · rfl
  calc
    _ = ∫⁻ ω, ∫⁻ z, F (ω,z) ∂ν ∂P := by
      apply lintegral_congr_ae
      filter_upwards [heq] with ω hω
      apply lintegral_congr
      intro z
      exact (hω z).symm
    _ = ∫⁻ z, ∫⁻ ω, F (ω,z) ∂P ∂ν := lintegral_lintegral_swap hF.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ A
      · have hz1 : ‖z‖ + ε ≤ 1 := by dsimp [A] at hz; linarith [hz.2]
        have hz2 : max ε ‖z‖ = ‖z‖ := max_eq_right (hεδ.trans hz.1)
        rw [Set.indicator_of_mem hz]
        calc
          (∫⁻ ω, F (ω,z) ∂P) = ∫⁻ ω, ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) ∂P := by
              apply lintegral_congr_ae
              filter_upwards [heq] with ω hω
              rw [hω z, Set.indicator_of_mem hz]
          _ = _ := by rw [lintegral_inserted_clock_density_eq hh hε γ α hz1, hz2]
      · rw [Set.indicator_of_notMem hz]
        simp [F, Set.indicator_of_notMem hz]

/-- Annular density occupation is bounded uniformly over small smoothing scales. -/
theorem exists_lintegral_annular_inserted_density_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {δ : ℝ} (hδ : 0 < δ)
    (γ α : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ δ → ε ≤ 1/2 →
      ∀ (ν : Measure ℂ) [SFinite ν],
      (∫⁻ ω, ∫⁻ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) z ∂ν ∂P) ≤
      ENNReal.ofReal M * ν univ := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  let f : ℂ → ℝ := fun z => Real.exp (-(γ * α) * Real.log (max δ ‖z‖))
  have hf : Continuous f := Real.continuous_exp.comp (continuous_const.mul
    ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hδ).ne')))
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (1/2 : ℝ)).bddAbove_image hf.continuousOn
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro ε hε hεδ hεhalf ν _
  rw [lintegral_annular_inserted_density_eq hh hε hεδ hεhalf γ α ν]
  calc
    _ ≤ ∫⁻ _ : ℂ, ENNReal.ofReal (max K 0) ∂ν := by
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ A
      · rw [Set.indicator_of_mem hz]
        have hzk : z ∈ Metric.closedBall (0 : ℂ) (1/2 : ℝ) := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
        have hle : f z ≤ K := hK ⟨z, hzk, rfl⟩
        dsimp [f] at hle
        rw [max_eq_right hz.1] at hle
        exact ENNReal.ofReal_le_ofReal (hle.trans (le_max_left _ _))
      · rw [Set.indicator_of_notMem hz]
        exact bot_le
    _ = _ := by simp

/-- The spatial occupation measure from a deterministic time to Brownian exit. -/
noncomputable def annularExitTailOccupation (D : Set ℂ) (T : ℝ) (b : ContinuousPath ℂ) : Measure ℂ :=
  Measure.map (fun t : ℝ => b t.toNNReal)
    (volume.restrict (Ioc T (ContinuousPath.exitTime D b).toReal))

/-- The annealed annular occupation after a horizon decays exponentially. -/
theorem exists_annular_exit_occupation_tail_le_exp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {D : Set ℂ}
    (hD : IsOpen D) (hDb : Bornology.IsBounded D) {δ : ℝ} (hδ : 0 < δ)
    (γ α : ℝ) :
    ∃ lam M : ℝ, 0 < lam ∧ 0 ≤ M ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ x : ℂ, ∀ T : ℝ, 0 ≤ T → ∀ {ε : ℝ}, 0 < ε → ε ≤ δ → ε ≤ 1/2 →
      (∫⁻ b, ∫⁻ ω, ∫⁻ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) z
        ∂(annularExitTailOccupation D T b) ∂P ∂planarBrownianMotion x) ≤
      ENNReal.ofReal M * (ENNReal.ofReal (lam⁻¹ * Real.exp (-lam * T)) * C) := by
  obtain ⟨M, hM, hbound⟩ := exists_lintegral_annular_inserted_density_le hh hδ γ α
  obtain ⟨lam, hlam, C, hC, htail⟩ :=
    exists_uniform_planarBrownianMotion_exitTime_excess_le_exp hD hDb
  refine ⟨lam, M, hlam, hM, C, hC, ?_⟩
  intro x T hT ε hε hεδ hεhalf
  calc
    _ ≤ ∫⁻ b, ENNReal.ofReal M *
        (ContinuousPath.exitTime D b - ENNReal.ofReal T) ∂planarBrownianMotion x := by
      apply lintegral_mono
      intro b
      let : IsFiniteMeasure (annularExitTailOccupation D T b) := by
        dsimp [annularExitTailOccupation]
        infer_instance
      have hν := hbound hε hεδ hεhalf (annularExitTailOccupation D T b)
      refine hν.trans ?_
      change ENNReal.ofReal M * annularExitTailOccupation D T b univ ≤
        ENNReal.ofReal M * (ContinuousPath.exitTime D b - ENNReal.ofReal T)
      gcongr
      have hm : annularExitTailOccupation D T b univ =
          ENNReal.ofReal ((ContinuousPath.exitTime D b).toReal - T) := by
        unfold annularExitTailOccupation
        have hmeas : Measurable (fun t : ℝ => b t.toNNReal) :=
          b.continuous.measurable.comp measurable_real_toNNReal
        rw [Measure.map_apply hmeas MeasurableSet.univ]
        simp [Real.volume_Ioc]
      rw [hm]
      by_cases hb : ContinuousPath.exitTime D b = ⊤
      · simp [hb]
      · rw [ENNReal.ofReal_sub _ hT, ENNReal.ofReal_toReal hb]
    _ = ENNReal.ofReal M *
        (∫⁻ b, ContinuousPath.exitTime D b - ENNReal.ofReal T ∂planarBrownianMotion x) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := by gcongr; exact htail x T hT

end HarmonicBalls
