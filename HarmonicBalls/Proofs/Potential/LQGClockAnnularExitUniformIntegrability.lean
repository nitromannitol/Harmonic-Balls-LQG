import HarmonicBalls.Proofs.Potential.LQGClockAnnularUniformIntegrability
import HarmonicBalls.Proofs.Potential.BrownianExpectedExitGreen
import MarkovProcess.Trajectory.ExitTimeExponentialMoment
import MarkovProcess.Path.ExitTimeShift
import LatticeProb.LQG.LQGCircleMoments
import HarmonicBalls.Proofs.Potential.BrownianIncrementRieszMoment

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

/-- Annular tail occupation is the annular density integral over the time interval. -/
theorem ae_annular_exit_tail_occupation_eq_time {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (γ α δ : ℝ) (D : Set ℂ) :
    ∀ᵐ ω ∂P, ∀ (b : ContinuousPath ℂ) (T : ℝ),
      (∫⁻ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) z
        ∂annularExitTailOccupation D T b) =
      ∫⁻ t in Ioc T (ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) (b t.toNNReal) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, Continuous (hcirc ω ε) := by
    filter_upwards [hHae] with ω hω
    rw [← funext (hω ε)]
    exact hHc ω ε hε
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  filter_upwards [hcont, ae_recentered_inserted_circle_average hh α] with ω hcont hrec b T
  have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z) =
      fun z => hcirc ω ε z - hcirc ω 1 0 - α * Real.log (max ε ‖z‖) := by
    funext z
    exact (hrec ε z hε).symm
  have hc : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z) := by
    rw [heq]
    exact (hcont.sub continuous_const).sub
      (continuous_const.mul ((continuous_const.max continuous_norm).log
        (fun _ => (lt_max_of_lt_left hε).ne')))
  have hf : Measurable (A.indicator (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) *
      Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)))) :=
    ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc))).measurable.ennreal_ofReal).indicator hA
  have hm : Measurable (fun t : ℝ => b t.toNNReal) :=
    b.continuous.measurable.comp measurable_real_toNNReal
  exact lintegral_map hf hm

/-- The annealed annular clock tail decays exponentially at Brownian exit. -/
theorem exists_annular_exit_time_tail_le_exp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {D : Set ℂ}
    (hD : IsOpen D) (hDb : Bornology.IsBounded D) {δ : ℝ} (hδ : 0 < δ)
    (γ α : ℝ) :
    ∃ lam M : ℝ, 0 < lam ∧ 0 ≤ M ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ x : ℂ, ∀ T : ℝ, 0 ≤ T → ∀ {ε : ℝ}, 0 < ε → ε ≤ δ → ε ≤ 1/2 →
      (∫⁻ b, ∫⁻ ω, ∫⁻ t in Ioc T (ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) (b t.toNNReal)
        ∂volume ∂P ∂planarBrownianMotion x) ≤
      ENNReal.ofReal M * (ENNReal.ofReal (lam⁻¹ * Real.exp (-lam * T)) * C) := by
  obtain ⟨lam, M, hlam, hM, C, hC, hbound⟩ :=
    exists_annular_exit_occupation_tail_le_exp hh hD hDb hδ γ α
  refine ⟨lam, M, hlam, hM, C, hC, ?_⟩
  intro x T hT ε hε hεδ hεhalf
  have htime := ae_annular_exit_tail_occupation_eq_time hh hε γ α δ D
  calc
    _ = ∫⁻ b, ∫⁻ ω, ∫⁻ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator
      (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) z
      ∂annularExitTailOccupation D T b ∂P ∂planarBrownianMotion x := by
        apply lintegral_congr
        intro b
        apply lintegral_congr_ae
        filter_upwards [htime] with ω hω
        exact (hω b T).symm
    _ ≤ _ := hbound x T hT hε hεδ hεhalf

/-- The expected unit Brownian Riesz energy does not depend on the starting point. -/
theorem integral_unitOccupationRieszEnergy_eq (x y : ℂ) {β : ℝ} (hβ0 : 0 < β) (hβ2 : β < 2) :
    (∫ b, unitOccupationRieszEnergy β b ∂planarBrownianMotion x) =
    ∫ b, unitOccupationRieszEnergy β b ∂planarBrownianMotion y := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let E : ContinuousPath ℂ → ℝ≥0∞ := fun b => ∫⁻ p : ℝ≥0 × ℝ≥0,
      (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-β) ∂(ν.prod ν)
  have hE : Measurable E := by
    apply Measurable.lintegral_prod_right
    fun_prop
  have hEx : ∀ᵐ b ∂planarBrownianMotion x, E b < ⊤ :=
    planarBrownianMotion_ae_unit_occupation_riesz_energy_lt_top x hβ0 hβ2
  have hEy : ∀ᵐ b ∂planarBrownianMotion y, E b < ⊤ :=
    planarBrownianMotion_ae_unit_occupation_riesz_energy_lt_top y hβ0 hβ2
  change (∫ b, (E b).toReal ∂planarBrownianMotion x) =
    ∫ b, (E b).toReal ∂planarBrownianMotion y
  rw [integral_toReal hE.aemeasurable hEx, integral_toReal hE.aemeasurable hEy]
  rw [show (∫⁻ b, E b ∂planarBrownianMotion x) =
    (∫⁻ b, E b ∂planarBrownianMotion y) from by
      rw [show (∫⁻ b, E b ∂planarBrownianMotion x) = _ from
        lintegral_planarBrownianMotion_pair_enorm_rpow_neg x β ν]
      rw [show (∫⁻ b, E b ∂planarBrownianMotion y) = _ from
        lintegral_planarBrownianMotion_pair_enorm_rpow_neg y β ν]]

/-- The expected extended unit Riesz energy is invariant under deterministic time shifts. -/
theorem lintegral_shift_unitOccupationRieszEnergy (x : ℂ) (s : ℝ≥0) (β : ℝ) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    (∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0,
      (ENNReal.ofReal ‖(ContinuousPath.shift s b) p.1 - (ContinuousPath.shift s b) p.2‖) ^ (-β)
        ∂(ν.prod ν) ∂planarBrownianMotion x) =
    ∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0,
      (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-β) ∂(ν.prod ν) ∂planarBrownianMotion x := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  dsimp only
  have hf : Measurable (fun q : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0) =>
      (ENNReal.ofReal ‖(ContinuousPath.shift s q.1) q.2.1 -
        (ContinuousPath.shift s q.1) q.2.2‖) ^ (-β)) := by
    simp only [ContinuousPath.shift_apply]
    fun_prop
  have hg : Measurable (fun q : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0) =>
      (ENNReal.ofReal ‖q.1 q.2.1 - q.1 q.2.2‖) ^ (-β)) := by fun_prop
  conv_lhs => rw [lintegral_lintegral_swap hf.aemeasurable]
  conv_rhs => rw [lintegral_lintegral_swap hg.aemeasurable]
  apply lintegral_congr
  intro p
  simp only [ContinuousPath.shift_apply]
  rw [lintegral_planarBrownianMotion_increment_enorm_rpow_neg_eq,
      lintegral_planarBrownianMotion_increment_enorm_rpow_neg_eq]
  congr 3
  simp

/-- Shifted unit energy is integrable with the same expectation. -/
theorem integrable_shift_unitOccupationRieszEnergy (x : ℂ) (s : ℝ≥0) {β : ℝ} (hβ0 : 0 < β) (hβ2 : β < 2) :
    Integrable (fun b => unitOccupationRieszEnergy β (ContinuousPath.shift s b))
        (planarBrownianMotion x) ∧
      (∫ b, unitOccupationRieszEnergy β (ContinuousPath.shift s b) ∂planarBrownianMotion x) =
        ∫ b, unitOccupationRieszEnergy β b ∂planarBrownianMotion x := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let E : ContinuousPath ℂ → ℝ≥0∞ := fun b => ∫⁻ p : ℝ≥0 × ℝ≥0,
      (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-β) ∂(ν.prod ν)
  have hE : Measurable E := by
    apply Measurable.lintegral_prod_right
    fun_prop
  have hEs : Measurable (fun b => E (ContinuousPath.shift s b)) :=
    hE.comp (ContinuousPath.measurable_shift_fixed s)
  have hfin : (∫⁻ b, E b ∂planarBrownianMotion x) < ⊤ :=
    planarBrownianMotion_unit_occupation_riesz_energy_lt_top x hβ0 hβ2
  have heq : (∫⁻ b, E (ContinuousPath.shift s b) ∂planarBrownianMotion x) =
      ∫⁻ b, E b ∂planarBrownianMotion x := lintegral_shift_unitOccupationRieszEnergy x s β
  have hfs : (∫⁻ b, E (ContinuousPath.shift s b) ∂planarBrownianMotion x) < ⊤ := by
    rw [heq]
    exact hfin
  have haes : ∀ᵐ b ∂planarBrownianMotion x, E (ContinuousPath.shift s b) < ⊤ :=
    ae_lt_top hEs hfs.ne
  have hae : ∀ᵐ b ∂planarBrownianMotion x, E b < ⊤ := ae_lt_top hE hfin.ne
  constructor
  · exact integrable_toReal_of_lintegral_ne_top hEs.aemeasurable hfs.ne
  · change (∫ b, (E (ContinuousPath.shift s b)).toReal ∂planarBrownianMotion x) =
      ∫ b, (E b).toReal ∂planarBrownianMotion x
    rw [integral_toReal hEs.aemeasurable haes, integral_toReal hE.aemeasurable hae, heq]

/-- Annular exit-time tails are summable along integer horizons and small scales. -/
theorem tsum_annular_exit_time_tails_lt_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {D : Set ℂ}
    (hD : IsOpen D) (hDb : Bornology.IsBounded D) {δ : ℝ} (hδ : 0 < δ)
    (γ α : ℝ) (x : ℂ) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n ∧ ε n ≤ δ ∧ ε n ≤ 1/2) :
    (∑' n : ℕ, ∫⁻ b, ∫⁻ ω, ∫⁻ t in Ioc (n : ℝ) (ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => ENNReal.ofReal ((ε n) ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε n) z))) (b t.toNNReal)
        ∂volume ∂P ∂planarBrownianMotion x) < ⊤ := by
  obtain ⟨lam, M, hlam, hM, C, hC, hbound⟩ :=
    exists_annular_exit_time_tail_le_exp hh hD hDb hδ γ α
  have hs : Summable (fun n : ℕ => lam⁻¹ * Real.exp (-lam * n)) := by
    have hgeom : Summable (fun n : ℕ => Real.exp ((-lam) * (n : ℝ))) :=
      by simpa only [mul_comm] using
        (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hlam))
    exact hgeom.mul_left lam⁻¹
  have ht : (∑' n : ℕ, ENNReal.ofReal (lam⁻¹ * Real.exp (-lam * n))) < ⊤ :=
    hs.tsum_ofReal_lt_top
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal M *
        (ENNReal.ofReal (lam⁻¹ * Real.exp (-lam * n)) * C) := by
      apply ENNReal.tsum_le_tsum
      intro n
      exact hbound x n (Nat.cast_nonneg n) (hε n).1 (hε n).2.1 (hε n).2.2
    _ = ENNReal.ofReal M * ((∑' n : ℕ,
        ENNReal.ofReal (lam⁻¹ * Real.exp (-lam * n))) * C) := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ht hC)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
private theorem uniform_block_exp_bound_algebra {u p d a q B C M I A : ℝ}
    (hB : 0 ≤ B)
    (hI : I ≤ C * Real.exp (u*d)) (hA : A ≤ M) :
    Real.exp (u*a) * ((B * Real.exp (-u*p) * I / Real.exp (u*((d-p)/2)) +
      Real.exp (u*((d-p)/2))) / 2 + 2*A*Real.exp (-u*q)) ≤
    (B*C+1)/2 * Real.exp (u*(a+(d-p)/2)) + 2*M*Real.exp (u*(a-q)) := by
  have h : B * Real.exp (-u*p) * I / Real.exp (u*((d-p)/2)) ≤
      B * Real.exp (-u*p) * (C * Real.exp (u*d)) / Real.exp (u*((d-p)/2)) := by
    gcongr
  have ha : 2*A*Real.exp (-u*q) ≤ 2*M*Real.exp (-u*q) := by gcongr
  calc
    _ ≤ Real.exp (u*a) * ((B * Real.exp (-u*p) * (C * Real.exp (u*d)) /
        Real.exp (u*((d-p)/2)) + Real.exp (u*((d-p)/2))) / 2 +
        2*M*Real.exp (-u*q)) := by gcongr
    _ = _ := by
      have h1 : Real.exp (u*a) * Real.exp (-u*p) * Real.exp (u*d) /
          Real.exp (u*((d-p)/2)) = Real.exp (u*(a+(d-p)/2)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
        congr 1
        ring
      have h2 : Real.exp (u*a) * Real.exp (u*((d-p)/2)) =
          Real.exp (u*(a+(d-p)/2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h3 : Real.exp (u*a) * Real.exp (-u*q) = Real.exp (u*(a-q)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      linear_combination (B*C/2)*h1 + (1/2)*h2 + (2*M)*h3


private theorem uniform_block_field_increment_le_rate
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε γ θ d C M : ℝ}
    (hε : 0 < ε) (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ}
    (hgm : Measurable g) (hg : Integrable g ν)
    (hgR : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ 1)
    (hγθ : γ ≤ θ) (hθ : θ ≤ 2 * γ)
    (hA : (∫ z, |g z| ∂ν) ≤ M)
    (hI : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(ν.prod ν)) ≤ C * Real.exp (Real.log ε * d)) :
    ∫ ω, |∫ z, g z * ((ε / 2) ^ (γ ^ 2 / 2) * Real.exp (γ * (hcirc ω (ε / 2) z - hcirc ω 1 0)) -
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * (hcirc ω ε z - hcirc ω 1 0))) ∂ν| ∂P ≤
      ((Real.exp (γ ^ 2 * Real.log 2) - 1) * C + 1) / 2 *
        Real.exp (Real.log ε * ((d - γ ^ 2 + (2 * γ - θ) ^ 2 / 2) / 2)) +
      2 * M * Real.exp (Real.log ε * ((θ - γ) ^ 2 / 2)) := by
  let p : ℝ := 2 * γ ^ 2 - (2 * γ - θ) ^ 2 / 2
  let q : ℝ := γ ^ 2 / 2 - (θ - γ) ^ 2 / 2
  let u : ℝ := Real.log ε
  have hB : 0 ≤ Real.exp (γ ^ 2 * Real.log 2) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hraw := hh.integral_abs_integral_increment_le hε (R := 1) zero_lt_one ν hgm hg hgR hγθ hθ
    (t := Real.exp (u * ((d - p) / 2))) (Real.exp_pos _)
  have hlog : Real.log (1 / ε) = -u := by simp [u]
  conv at hraw =>
    rhs
    rw [hlog, Real.rpow_def_of_pos hε]
  have halg := uniform_block_exp_bound_algebra (u := u) (p := p) (d := d) (a := γ ^ 2 / 2)
    (q := q) (B := Real.exp (γ ^ 2 * Real.log 2) - 1) hB hI hA
  refine hraw.trans ?_
  convert halg using 1; dsimp [p, q, u]; ring_nf

private theorem uniform_block_brownian_field_submeasure_riesz_increment_rate
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (x : ℂ)
    {g : ℂ → ℝ} (hg : Measurable g) {M : ℝ} (hM : 0 ≤ M)
    (hgM : ∀ z, |g z| ≤ M) (hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ 1 / 2)
    (θ d : ℝ) (hγθ : γ < θ) (hθ : θ < 2*γ)
    (hd0 : 0 < d) (hd2 : d < 2) :
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ᵐ b ∂(planarBrownianMotion x),
        ∀ μ : Measure ℂ, μ ≤ Measure.map (fun t => b t) ν →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
        (∫ ω, |∫ z, g z * ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0)) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0))) ∂μ| ∂P) ≤
        ((Real.exp (γ^2*Real.log 2)-1)*(M^2 * unitOccupationRieszEnergy d b * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  filter_upwards [planarBrownianMotion_ae_unit_weighted_occupation_le_riesz_energy x hd0 hd2] with b hb
  intro μ hμ ε hε hεhalf
  let ρ : Measure ℂ := Measure.map (fun t => b t) ν
  let : IsProbabilityMeasure ρ := inferInstance
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le ρ hμ
  have hgρ : Integrable g ρ := by
    refine (integrable_const M).mono' hg.aestronglyMeasurable ?_
    filter_upwards with z
    simpa [Real.norm_eq_abs] using hgM z
  have hgi : Integrable g μ := hgρ.mono_measure hμ
  have hA : (∫ z, |g z| ∂μ) ≤ M := by
    calc
      _ ≤ ∫ z, |g z| ∂ρ := integral_mono_measure hμ (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) hgρ.abs
      _ ≤ ∫ _ : ℂ, M ∂ρ := integral_mono hgρ.abs (integrable_const M) (fun z => hgM z)
      _ = M := by simp
  have hpair0 := hb g hg M hM hgM (2*ε) (by positivity)
  have hpair : (∫ p : ℂ × ℂ, if ‖p.1-p.2‖ < 2*ε then |g p.1| * |g p.2| else 0
      ∂(μ.prod μ)) ≤ M^2*(unitOccupationRieszEnergy d b*(2*ε)^d) := by
    apply (integral_mono_measure (Measure.prod_mono hμ hμ) ?_ hpair0.1).trans hpair0.2.2
    filter_upwards with p
    split_ifs <;> positivity
  have hI : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤
      (M^2*unitOccupationRieszEnergy d b*2^d)*Real.exp (Real.log ε*d) := by
    have hI' : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤ M^2*(unitOccupationRieszEnergy d b*(2*ε)^d) := by
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using hpair
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le,
      Real.rpow_def_of_pos hε] at hI'
    convert hI' using 1; ring
  exact uniform_block_field_increment_le_rate hh hε μ hg hgi (fun z hz => by linarith [hgs z hz])
    hγθ.le hθ.le hA hI

private theorem uniform_block_annular_weight_bound {δ γ α : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ,
      |({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => Real.exp (-γ*α*Real.log (max δ ‖z‖))) z)| ≤ M := by
  let f : ℂ → ℝ := fun z => Real.exp (-γ*α*Real.log (max δ ‖z‖))
  have hf : Continuous f := by
    exact Real.continuous_exp.comp (continuous_const.mul
      ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hδ).ne')))
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (1/2 : ℝ)).bddAbove_image hf.continuousOn
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro z
  by_cases hz : z ∈ {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  · have hzk : z ∈ Metric.closedBall (0 : ℂ) (1/2 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
    have hle : f z ≤ K := hK ⟨z, hzk, rfl⟩
    rw [Set.indicator_of_mem hz, abs_of_pos (Real.exp_pos _)]
    exact hle.trans (le_max_left K 0)
  · rw [Set.indicator_of_notMem hz, abs_zero]
    exact le_max_right K 0




theorem ae_brownian_stopped_annular_increment_le_riesz_energy_uniform_start
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ x : ℂ,
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ᵐ b ∂(planarBrownianMotion x),
        ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ε ≤ δ →
        let μ := Measure.map (fun t => b t) (ν.restrict (Iic T))
        (∫ ω, |∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0 - α*Real.log (max (ε/2) ‖z‖))) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0 - α*Real.log (max ε ‖z‖)))) z ∂μ| ∂P) ≤
        ((Real.exp (γ^2*Real.log 2)-1)*(M^2 * unitOccupationRieszEnergy d b * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  let g : ℂ → ℝ := A.indicator (fun z => Real.exp (-γ*α*Real.log (max δ ‖z‖)))
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hgm : Measurable g := by
    apply Measurable.indicator _ hA
    exact (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hδ).ne')))).measurable
  obtain ⟨M, hM, hgM⟩ := uniform_block_annular_weight_bound (γ := γ) (α := α) hδ
  have hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ 1/2 := by
    intro z hz
    by_contra h
    have hn : z ∉ A := fun hzA => h hzA.2
    exact hz (Set.indicator_of_notMem hn _)
  obtain ⟨θ, d, hγθ, hθ, hd0, hd2, hp, _⟩ :=
    exists_clock_truncation_exponents hγ0 hγ2
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro x
  have hb := uniform_block_brownian_field_submeasure_riesz_increment_rate
    hh x hgm hM hgM hgs θ d hγθ hθ hd0 hd2
  filter_upwards [hb] with b hb
  intro T ε hε hεhalf hεδ
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let μ := Measure.map (fun t => b t) (ν.restrict (Iic T))
  have hμ : μ ≤ Measure.map (fun t => b t) ν :=
    Measure.map_mono Measure.restrict_le_self b.continuous.measurable
  have hbound := hb μ hμ ε hε hεhalf
  refine (le_of_eq ?_).trans hbound
  congr 1
  funext ω
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ A
  · have hδε : ε ≤ ‖z‖ := hεδ.trans hz.1
    have hhalf : ε/2 ≤ ‖z‖ := by linarith
    rw [show A.indicator _ z = _ from Set.indicator_of_mem hz _,
      show g z = _ from Set.indicator_of_mem hz _, max_eq_right hz.1,
      max_eq_right hδε, max_eq_right hhalf]
    have heq (r : ℝ) : γ * (hcirc ω r z - hcirc ω 1 0 - α * Real.log ‖z‖) =
        -γ*α*Real.log ‖z‖ + γ*(hcirc ω r z-hcirc ω 1 0) := by ring
    rw [heq (ε/2), heq ε, Real.exp_add, Real.exp_add]
    ring
  · rw [show A.indicator _ z = _ from Set.indicator_of_notMem hz _,
      show g z = _ from Set.indicator_of_notMem hz _, zero_mul]



/-- Events holding for Brownian motion from every start also hold after a time shift. -/
theorem ae_planarBrownianMotion_shift_of_forall_ae (x : ℂ) (s : ℝ≥0) (S : Set (ContinuousPath ℂ)) (hS : MeasurableSet S)
    (h : ∀ y : ℂ, ∀ᵐ b ∂planarBrownianMotion y, b ∈ S) :
    ∀ᵐ b ∂planarBrownianMotion x, ContinuousPath.shift s b ∈ S := by
  have ha : ∀ᵐ b ∂(planarBrownianMotion x).map (ContinuousPath.shift s), b ∈ S := by
    rw [planarBrownianMotion_eq_continuousProcess]
    have hshift := congrArg (fun K => K x)
      (SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_shift
        planarHeatSemigroup isConservative_planarHeatSemigroup
        isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup s)
    rw [ProbabilityTheory.Kernel.map_apply _ (ContinuousPath.measurable_shift_fixed s) x] at hshift
    rw [hshift]
    apply ProbabilityTheory.Kernel.ae_comp_of_ae_ae hS
    filter_upwards with y
    change ∀ᵐ b ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess
      planarHeatSemigroup isConservative_planarHeatSemigroup y), b ∈ S
    rw [← planarBrownianMotion_eq_continuousProcess]
    exact h y
  exact (ae_map_iff (ContinuousPath.measurable_shift_fixed s).aemeasurable hS).mp ha

/-- Shifted annular increments satisfy the shared Riesz-energy envelope. -/
theorem ae_shift_stopped_annular_increment_le_riesz_energy {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ (x : ℂ) (s : ℝ≥0) (τ : ContinuousPath ℂ → ℝ≥0), Measurable τ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ε ≤ δ →
        ∀ᵐ b ∂planarBrownianMotion x,
        stoppedAnnularIncrement P hcirc γ α δ ε τ (ContinuousPath.shift s b) ≤
        ((Real.exp (γ^2*Real.log 2)-1)*(M^2 *
          unitOccupationRieszEnergy d (ContinuousPath.shift s b) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    ae_brownian_stopped_annular_increment_le_riesz_energy_uniform_start hh hγ0 hγ2 α hδ
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro x s τ hτ ε hε hεhalf hεδ
  let F := stoppedAnnularIncrement P hcirc γ α δ ε τ
  let G : ContinuousPath ℂ → ℝ := fun b =>
    ((Real.exp (γ^2*Real.log 2)-1)*(M^2 * unitOccupationRieszEnergy d b * 2^d)+1)/2 *
      Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
    2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))
  have hF : Measurable F := measurable_stopped_annular_inserted_field_expectation hh hε γ α δ τ hτ
  have hG : Measurable G := by
    dsimp [G]
    have hE := measurable_unitOccupationRieszEnergy d
    fun_prop
  have hS : MeasurableSet {b | F b ≤ G b} := measurableSet_le hF hG
  apply ae_planarBrownianMotion_shift_of_forall_ae x s _ hS
  intro y
  filter_upwards [hb y] with b hb'
  exact hb' (τ b) ε hε hεhalf hεδ

/-- Shifted stopped annular increments have a common annealed geometric-rate bound. -/
theorem brownian_shift_stopped_annular_increment_annealed_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ (x : ℂ) (s : ℝ≥0) (τ : ContinuousPath ℂ → ℝ≥0), Measurable τ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ε ≤ δ →
        Integrable (fun b => stoppedAnnularIncrement P hcirc γ α δ ε τ
          (ContinuousPath.shift s b)) (planarBrownianMotion x) ∧
        (∫ b, stoppedAnnularIncrement P hcirc γ α δ ε τ (ContinuousPath.shift s b)
          ∂planarBrownianMotion x) ≤
        ((Real.exp (γ^2*Real.log 2)-1) *
          (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    ae_shift_stopped_annular_increment_le_riesz_energy hh hγ0 hγ2 α hδ
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro x s τ hτ ε hε hεhalf hεδ
  let E : ContinuousPath ℂ → ℝ := fun b => unitOccupationRieszEnergy d (ContinuousPath.shift s b)
  let a : ℝ := Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2))
  let c : ℝ := Real.exp (Real.log ε * ((θ-γ)^2/2))
  let B : ℝ := Real.exp (γ^2*Real.log 2)-1
  let G : ContinuousPath ℂ → ℝ := fun b => ((B*(M^2 * E b * 2^d)+1)/2)*a + 2*M*c
  have hE : Integrable E (planarBrownianMotion x) :=
    (integrable_shift_unitOccupationRieszEnergy x s hd0 hd2).1
  have hG : Integrable G (planarBrownianMotion x) := by
    dsimp [G]
    fun_prop
  have hm : Measurable (fun b => stoppedAnnularIncrement P hcirc γ α δ ε τ
      (ContinuousPath.shift s b)) :=
    (measurable_stopped_annular_inserted_field_expectation hh hε γ α δ τ hτ).comp
      (ContinuousPath.measurable_shift_fixed s)
  have hle : ∀ᵐ b ∂planarBrownianMotion x,
      stoppedAnnularIncrement P hcirc γ α δ ε τ (ContinuousPath.shift s b) ≤ G b :=
    hb x s τ hτ ε hε hεhalf hεδ
  have hn : ∀ b, 0 ≤ stoppedAnnularIncrement P hcirc γ α δ ε τ b := by
    intro b
    apply integral_nonneg
    intro ω
    exact abs_nonneg _
  have hi : Integrable (fun b => stoppedAnnularIncrement P hcirc γ α δ ε τ
      (ContinuousPath.shift s b)) (planarBrownianMotion x) := by
    apply hG.mono' hm.aestronglyMeasurable
    filter_upwards [hle] with b hb
    simpa [Real.norm_eq_abs, abs_of_nonneg (hn _)] using hb
  refine ⟨hi, (integral_mono_ae hi hG hle).trans ?_⟩
  change (∫ b, G b ∂planarBrownianMotion x) ≤
    ((B*(M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2)*a + 2*M*c
  have hGeq : G = fun b => (B*M^2*2^d*a/2)*E b + (a/2 + 2*M*c) := by
    funext b
    dsimp [G]
    ring
  rw [hGeq, integral_add (hE.const_mul _) (integrable_const _), integral_const_mul]
  have hEx : (∫ b, E b ∂planarBrownianMotion x) =
      ∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0 :=
    (integrable_shift_unitOccupationRieszEnergy x s hd0 hd2).2.trans
      (integral_unitOccupationRieszEnergy_eq x 0 hd0 hd2)
  rw [hEx]
  simp only [integral_const, smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one, one_mul]
  ring_nf
  exact le_rfl

/-- Annular density increments up to the shifted Brownian exit have a common rate bound. -/
theorem brownian_shift_exit_annular_increment_annealed_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ (x : ℂ) (s : ℝ≥0) (ε : ℝ), 0 < ε → ε ≤ 1/2 → ε ≤ δ →
        Integrable (fun b => ∫ ω, |∫ t in (0 : ℝ)..
          (min (1 : ℝ≥0) (ContinuousPath.exitTime D (ContinuousPath.shift s b)).toNNReal : ℝ),
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
            ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
              ((ContinuousPath.shift s b) t.toNNReal)| ∂P) (planarBrownianMotion x) ∧
        (∫ b, ∫ ω, |∫ t in (0 : ℝ)..
          (min (1 : ℝ≥0) (ContinuousPath.exitTime D (ContinuousPath.shift s b)).toNNReal : ℝ),
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
            ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
              ((ContinuousPath.shift s b) t.toNNReal)| ∂P ∂planarBrownianMotion x) ≤
        ((Real.exp (γ^2*Real.log 2)-1) *
          (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_shift_stopped_annular_increment_annealed_le hh hγ0 hγ2 α hδ
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro x s ε hε hεhalf hεδ
  let τ : ContinuousPath ℂ → ℝ≥0 := fun b => (ContinuousPath.exitTime D b).toNNReal
  have hτ : Measurable τ := (ContinuousPath.measurable_exitTime D hD).ennreal_toNNReal
  have h := hb x s τ hτ ε hε hεhalf hεδ
  convert h using 1 <;>
    simp only [stoppedAnnularIncrement_eq_time_integral hh hε γ α δ τ, τ]

/-- Before exit, the shifted exit integral equals the corresponding stopped block. -/
theorem intervalIntegral_shift_exit_eq_stopped_block (D : Set ℂ) (b : ContinuousPath ℂ) (s : ℝ≥0)
    (hfin : ContinuousPath.exitTime D b ≠ ⊤)
    (hs : (s : ℝ≥0∞) < ContinuousPath.exitTime D b) (f : ℂ → ℝ) :
    (∫ t in (0 : ℝ)..(min (1 : ℝ≥0) (ContinuousPath.exitTime D
        (ContinuousPath.shift s b)).toNNReal : ℝ), f ((ContinuousPath.shift s b) t.toNNReal)) =
    ∫ t in (s : ℝ)..min ((s : ℝ) + 1) (ContinuousPath.exitTime D b).toReal, f (b t.toNNReal) := by
  have hadd := ContinuousPath.exitTime_shift_add D b s hs
  have hshiftfin : ContinuousPath.exitTime D (ContinuousPath.shift s b) ≠ ⊤ := by
    intro h
    rw [h] at hadd
    simp only [top_add] at hadd
    exact hfin hadd.symm
  have hr : (ContinuousPath.exitTime D (ContinuousPath.shift s b)).toReal + (s : ℝ) =
      (ContinuousPath.exitTime D b).toReal := by
    have h := congrArg ENNReal.toReal hadd
    simpa only [ENNReal.toReal_add hshiftfin ENNReal.coe_ne_top, ENNReal.coe_toReal] using h
  let u : ℝ := (min (1 : ℝ≥0) (ContinuousPath.exitTime D
      (ContinuousPath.shift s b)).toNNReal : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have huend : (s : ℝ) + u = min ((s : ℝ) + 1) (ContinuousPath.exitTime D b).toReal := by
    dsimp [u]
    rw [ENNReal.coe_toNNReal_eq_toReal, add_min]
    rw [add_comm (s : ℝ) (ContinuousPath.exitTime D (ContinuousPath.shift s b)).toReal, hr]
  calc
    _ = ∫ t in (0 : ℝ)..u, f (b (((s : ℝ) + t).toNNReal)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hu] at ht
      simp only [ContinuousPath.shift_apply, Real.toNNReal_add s.coe_nonneg ht.1, Real.toNNReal_coe]
    _ = ∫ t in (s : ℝ)..(s : ℝ) + u, f (b t.toNNReal) := by
      simpa only [add_zero] using (intervalIntegral.integral_comp_add_left
        (fun t : ℝ => f (b t.toNNReal)) (s : ℝ) (a := 0) (b := u))
    _ = _ := by rw [huend]

/-- A stopped block is empty after exit and equals the shifted integral before exit. -/
theorem setIntegral_exit_stopped_block_eq (D : Set ℂ) (b : ContinuousPath ℂ) (s : ℝ≥0)
    (hfin : ContinuousPath.exitTime D b ≠ ⊤) (f : ℂ → ℝ) :
    (∫ t in Ioc (s : ℝ) (min ((s : ℝ) + 1) (ContinuousPath.exitTime D b).toReal),
      f (b t.toNNReal)) =
    if (s : ℝ≥0∞) < ContinuousPath.exitTime D b then
      ∫ t in (0 : ℝ)..(min (1 : ℝ≥0) (ContinuousPath.exitTime D
        (ContinuousPath.shift s b)).toNNReal : ℝ), f ((ContinuousPath.shift s b) t.toNNReal)
    else 0 := by
  by_cases hs : (s : ℝ≥0∞) < ContinuousPath.exitTime D b
  · rw [ite_eq_left hs]
    have hle : (s : ℝ) ≤ (ContinuousPath.exitTime D b).toReal := by
      have := (ENNReal.toReal_le_toReal ENNReal.coe_ne_top hfin).2 hs.le
      simpa only [ENNReal.coe_toReal] using this
    rw [← intervalIntegral.integral_of_le (le_min (by linarith) hle)]
    exact (intervalIntegral_shift_exit_eq_stopped_block D b s hfin hs f).symm
  · rw [ite_eq_right hs]
    have hle : (ContinuousPath.exitTime D b).toReal ≤ (s : ℝ) := by
      have := (ENNReal.toReal_le_toReal hfin ENNReal.coe_ne_top).2 (not_lt.mp hs)
      simpa only [ENNReal.coe_toReal] using this
    simp [Set.Ioc_eq_empty (not_lt.mpr (le_trans (min_le_right _ _) hle))]

/-- The field-averaged absolute annular increment on a stopped unit block. -/
noncomputable def annularExitBlockIncrement {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hcirc : Ω → ℝ → ℂ → ℝ) (γ α δ ε : ℝ) (D : Set ℂ) (s : ℝ≥0)
    (b : ContinuousPath ℂ) : ℝ :=
  ∫ ω, |∫ t in Ioc (s : ℝ) (min ((s : ℝ) + 1) (ContinuousPath.exitTime D b).toReal),
    {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
      (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
      ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
        (b t.toNNReal)| ∂P

/-- Stopped annular block increments obey a shared annealed rate bound. -/
theorem brownian_annular_exit_block_increment_annealed_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ (x : ℂ) (s : ℝ≥0) (ε : ℝ), 0 < ε → ε ≤ 1/2 → ε ≤ δ →
        Integrable (annularExitBlockIncrement P hcirc γ α δ ε D s) (planarBrownianMotion x) ∧
        (∫ b, annularExitBlockIncrement P hcirc γ α δ ε D s b ∂planarBrownianMotion x) ≤
        ((Real.exp (γ^2*Real.log 2)-1) *
          (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_shift_stopped_annular_increment_annealed_le hh hγ0 hγ2 α hδ
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro x s ε hε hεhalf hεδ
  let τ : ContinuousPath ℂ → ℝ≥0 := fun b => (ContinuousPath.exitTime D b).toNNReal
  have hτ : Measurable τ := (ContinuousPath.measurable_exitTime D hD).ennreal_toNNReal
  let F : ContinuousPath ℂ → ℝ := fun b =>
    stoppedAnnularIncrement P hcirc γ α δ ε τ (ContinuousPath.shift s b)
  let S : Set (ContinuousPath ℂ) := {b | (s : ℝ≥0∞) < ContinuousPath.exitTime D b}
  have hS : MeasurableSet S := measurableSet_lt measurable_const (ContinuousPath.measurable_exitTime D hD)
  have hF := hb x s τ hτ ε hε hεhalf hεδ
  have heq : annularExitBlockIncrement P hcirc γ α δ ε D s =ᵐ[planarBrownianMotion x] S.indicator F := by
    filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top x hDb] with b hfin
    by_cases hs : (s : ℝ≥0∞) < ContinuousPath.exitTime D b
    · rw [Set.indicator_of_mem (show b ∈ S from hs)]
      rw [show F b = _ from stoppedAnnularIncrement_eq_time_integral hh hε γ α δ τ _]
      apply integral_congr_ae
      filter_upwards with ω
      congr 1
      exact setIntegral_exit_stopped_block_eq D b s hfin.ne _ |>.trans (ite_eq_left hs)
    · rw [Set.indicator_of_notMem (show b ∉ S from hs)]
      dsimp [annularExitBlockIncrement]
      apply integral_eq_zero_of_ae
      filter_upwards with ω
      rw [setIntegral_exit_stopped_block_eq D b s hfin.ne _, ite_eq_right hs, abs_zero]
      rfl
  have hi := (hF.1.indicator hS).congr heq.symm
  refine ⟨hi, (integral_mono_ae hi hF.1 ?_).trans hF.2⟩
  filter_upwards [heq] with b heq
  rw [heq]
  by_cases hs : b ∈ S
  · rw [Set.indicator_of_mem hs]
  · rw [Set.indicator_of_notMem hs]
    apply integral_nonneg
    intro ω
    exact abs_nonneg _

/-- A stopped time integral decomposes over integer unit blocks. -/
theorem intervalIntegral_stopped_eq_sum_blocks (f : ℝ → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (N : ℕ)
    (hf : IntervalIntegrable f volume 0 τ) :
    (∫ t in (0 : ℝ)..min (N : ℝ) τ, f t) =
    ∑ k ∈ Finset.range N, ∫ t in Ioc (k : ℝ) (min ((k : ℝ) + 1) τ), f t := by
  let a : ℕ → ℝ := fun k => min (k : ℝ) τ
  have hmono : Monotone a := by
    intro k l hkl
    exact min_le_min_right τ (Nat.cast_le.mpr hkl)
  have hbound : ∀ k, 0 ≤ a k ∧ a k ≤ τ := by
    intro k
    exact ⟨le_min (Nat.cast_nonneg k) hτ, min_le_right _ _⟩
  have hint : ∀ k < N, IntervalIntegrable f volume (a k) (a (k+1)) := by
    intro k hk
    apply hf.mono_set
    rw [uIcc_of_le (hmono (Nat.le_succ k)), uIcc_of_le hτ]
    exact Icc_subset_Icc (hbound k).1 (hbound (k+1)).2
  have heq := intervalIntegral.sum_integral_adjacent_intervals hint
  have ha0 : a 0 = 0 := by simp [a, min_eq_left hτ]
  rw [ha0] at heq
  change (∑ k ∈ Finset.range N, ∫ t in a k..a (k+1), f t) =
    ∫ t in (0 : ℝ)..min (N : ℝ) τ, f t at heq
  rw [← heq]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkτ : (k : ℝ) ≤ τ
  · rw [show a k = k from min_eq_left hkτ]
    rw [intervalIntegral.integral_of_le (by
      dsimp [a]
      refine le_min ?_ hkτ
      exact_mod_cast Nat.le_succ k)]
    congr 1
    simp [a, Nat.cast_add]
  · have hτk : τ ≤ (k : ℝ) := le_of_not_ge hkτ
    have hτk1 : τ ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h1 : a k = τ := min_eq_right hτk
    have h2 : a (k+1) = τ := min_eq_right hτk1
    rw [h1, h2, intervalIntegral.integral_same]
    have h' : min ((k : ℝ) + 1) τ ≤ (k : ℝ) := (min_le_right _ _).trans hτk
    simp [Ioc_eq_empty (not_lt.mpr h')]

/-- Continuous annular densities are integrable on every bounded time interval. -/
theorem intervalIntegrable_annular_density (f : ℂ → ℝ) (hf : Continuous f) (δ : ℝ)
    (b : ContinuousPath ℂ) (a c : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b t.toNNReal)) volume a c := by
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
  have ht : Measurable (fun t : ℝ => g (b t.toNNReal)) :=
    hg.comp (b.continuous.measurable.comp measurable_real_toNNReal)
  rw [intervalIntegrable_iff]
  let : IsFiniteMeasure (volume.restrict (uIoc a c)) :=
    Real.isFiniteMeasure_restrict_Ioc _ _
  apply (integrable_const (max K 0)).mono' ht.aestronglyMeasurable
  filter_upwards with t
  exact hgK (b t.toNNReal)

/-- A stopped annular block increment is integrable over the field. -/
theorem integrable_annular_exit_block_increment_field {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε δ : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hεδ : ε ≤ δ)
    (γ α : ℝ) (D : Set ℂ) (s : ℝ≥0) (b : ContinuousPath ℂ)
    (hfin : ContinuousPath.exitTime D b ≠ ⊤) :
    Integrable (fun ω => ∫ t in Ioc (s : ℝ)
      (min ((s : ℝ) + 1) (ContinuousPath.exitTime D b).toReal),
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
            (b t.toNNReal)) P := by
  by_cases hs : (s : ℝ≥0∞) < ContinuousPath.exitTime D b
  · let τ : ContinuousPath ℂ → ℝ≥0 := fun p => (ContinuousPath.exitTime D p).toNNReal
    let q := ContinuousPath.shift s b
    have hi := integrable_stopped_annular_increment_field hh hε hεhalf hεδ γ α τ q
    apply hi.congr
    filter_upwards [ae_annular_inserted_occupation_eq_time_integral hh hε γ α δ,
      ae_recentered_inserted_circle_average hh α] with ω htime hrec
    have hraw : (∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0 - α*Real.log (max (ε/2) ‖z‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0 - α*Real.log (max ε ‖z‖)))) z
      ∂(Measure.map (fun t => q t) ((Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ q))))) =
      ∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
        ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) z
      ∂(Measure.map (fun t => q t) ((Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ q)))) := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [Set.indicator_apply]
      split_ifs
      · rw [hrec (ε/2) z (half_pos hε), hrec ε z hε]
      · rfl
    rw [hraw, htime q (τ q)]
    exact (setIntegral_exit_stopped_block_eq D b s hfin _).trans (ite_eq_left hs) |>.symm
  · have hz : (fun ω => ∫ t in Ioc (s : ℝ)
        (min ((s : ℝ) + 1) (ContinuousPath.exitTime D b).toReal),
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
            (b t.toNNReal)) = 0 := by
      funext ω
      rw [setIntegral_exit_stopped_block_eq D b s hfin _, ite_eq_right hs]
      rfl
    rw [hz]
    exact integrable_zero _ _ _

/-- The field-averaged annular increment up to a stopped integer horizon. -/
noncomputable def annularExitHorizonIncrement {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hcirc : Ω → ℝ → ℂ → ℝ) (γ α δ ε : ℝ) (D : Set ℂ) (N : ℕ)
    (b : ContinuousPath ℂ) : ℝ :=
  ∫ ω, |∫ t in (0 : ℝ)..min (N : ℝ) (ContinuousPath.exitTime D b).toReal,
    {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
      (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
      ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
        (b t.toNNReal)| ∂P

/-- The field-averaged stopped increment is bounded by its unit-block increments. -/
theorem annular_exit_horizon_increment_le_sum_blocks {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε δ : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hεδ : ε ≤ δ)
    (γ α : ℝ) (D : Set ℂ) (N : ℕ) (b : ContinuousPath ℂ)
    (hfin : ContinuousPath.exitTime D b ≠ ⊤) :
    annularExitHorizonIncrement P hcirc γ α δ ε D N b ≤
      ∑ k ∈ Finset.range N, annularExitBlockIncrement P hcirc γ α δ ε D k b := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  let G : Ω → ℂ → ℝ := fun ω z =>
    (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
    ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)
  let F : Ω → ℝ := fun ω => ∫ t in (0 : ℝ)..min (N : ℝ) (ContinuousPath.exitTime D b).toReal,
    A.indicator (G ω) (b t.toNNReal)
  let B : ℕ → Ω → ℝ := fun k ω => ∫ t in Ioc (k : ℝ)
      (min ((k : ℝ) + 1) (ContinuousPath.exitTime D b).toReal), A.indicator (G ω) (b t.toNNReal)
  have hB : ∀ k, Integrable (B k) P := by
    intro k
    exact integrable_annular_exit_block_increment_field hh hε hεhalf hεδ γ α D k b hfin
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  have hsum : F =ᵐ[P] fun ω => ∑ k ∈ Finset.range N, B k ω := by
    filter_upwards [hcont, ae_recentered_inserted_circle_average hh α] with ω hcont hrec
    have hc (r : ℝ) (hr : 0 < r) : Continuous (fun z =>
        r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)) := by
      have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) =
          fun z => hcirc ω r z - hcirc ω 1 0 - α * Real.log (max r ‖z‖) := by
        funext z
        exact (hrec r z hr).symm
      have hc' : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) := by
        rw [heq]
        exact ((hcont r hr).sub continuous_const).sub (continuous_const.mul
          ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hr).ne')))
      exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc'))
    have hG : Continuous (G ω) := (hc (ε/2) (half_pos hε)).sub (hc ε hε)
    have hint := intervalIntegrable_annular_density (G ω) hG δ b 0
      (ContinuousPath.exitTime D b).toReal
    exact intervalIntegral_stopped_eq_sum_blocks _ _ ENNReal.toReal_nonneg N hint
  have hsumint : Integrable (fun ω => ∑ k ∈ Finset.range N, B k ω) P := by
    exact integrable_finsetSum _ (fun k hk => hB k)
  have hF : Integrable F P := hsumint.congr hsum.symm
  have hsumabs : Integrable (fun ω => ∑ k ∈ Finset.range N, |B k ω|) P := by
    exact integrable_finsetSum _ (fun k hk => (hB k).abs)
  change (∫ ω, |F ω| ∂P) ≤ ∑ k ∈ Finset.range N, ∫ ω, |B k ω| ∂P
  calc
    _ ≤ ∫ ω, ∑ k ∈ Finset.range N, |B k ω| ∂P := by
      apply integral_mono_ae hF.abs hsumabs
      filter_upwards [hsum] with ω hω
      rw [hω]
      exact Finset.abs_sum_le_sum_abs _ _
    _ = _ := integral_finsetSum _ (fun k hk => (hB k).abs)

/-- The stopped annular increment has a jointly measurable field-path version. -/
theorem exists_measurable_annular_exit_horizon_sample {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (γ α δ : ℝ) {D : Set ℂ} (hD : IsOpen D) (N : ℕ) :
    ∃ F : ContinuousPath ℂ × Ω → ℝ, Measurable F ∧ ∀ᵐ ω ∂P, ∀ b,
      F (b,ω) = ∫ t in (0 : ℝ)..min (N : ℝ) (ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
            (b t.toNNReal) := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let J : Ω × ℂ → ℝ := fun q => A.indicator (fun z =>
    (ε/2)^(γ^2/2) * Real.exp (γ*(H q.1 (ε/2) z-H q.1 1 0 - α*Real.log (max (ε/2) ‖z‖))) -
    ε^(γ^2/2) * Real.exp (γ*(H q.1 ε z-H q.1 1 0 - α*Real.log (max ε ‖z‖)))) q.2
  have h1 : Measurable (fun q : Ω × ℂ => H q.1 (ε/2) q.2) :=
    (hHm (ε/2) (half_pos hε)).comp measurable_swap
  have h2 : Measurable (fun q : Ω × ℂ => H q.1 ε q.2) := (hHm ε hε).comp measurable_swap
  have h3 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
    (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
  have hJ : Measurable J := by
    apply Measurable.indicator _ (hA.preimage measurable_snd)
    exact (measurable_const.mul (measurable_const.mul ((h1.sub h3).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp).sub
      (measurable_const.mul (measurable_const.mul ((h2.sub h3).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp)
  let U : ContinuousPath ℂ → ℝ := fun b => min (N : ℝ) (ContinuousPath.exitTime D b).toReal
  have hU : Measurable U := measurable_const.min ((ContinuousPath.measurable_exitTime D hD).ennreal_toReal)
  have heval : Measurable (fun q : (ContinuousPath ℂ × Ω) × ℝ => q.1.1 q.2.toNNReal) := by
    exact (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk (measurable_fst.comp measurable_fst))
  let S : Set ((ContinuousPath ℂ × Ω) × ℝ) := {q | 0 < q.2 ∧ q.2 ≤ U q.1.1}
  have hS : MeasurableSet S := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (hU.comp (measurable_fst.comp measurable_fst)))
  let Q : (ContinuousPath ℂ × Ω) × ℝ → ℝ := fun q =>
    S.indicator (fun q => J (q.1.2, q.1.1 q.2.toNNReal)) q
  have hQ : Measurable Q := by
    exact (hJ.comp ((measurable_snd.comp measurable_fst).prodMk heval)).indicator hS
  refine ⟨fun q => ∫ t, Q (q,t), hQ.stronglyMeasurable.integral_prod_right'.measurable, ?_⟩
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec b
  have hU0 : 0 ≤ U b := le_min (Nat.cast_nonneg N) ENNReal.toReal_nonneg
  rw [intervalIntegral.integral_of_le hU0, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Q, S, U, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Ioc, J, A]
  split_ifs with ht hz
  · rw [hω (ε/2) (b t.toNNReal), hω ε (b t.toNNReal), hω 1 0,
      hrec (ε/2) (b t.toNNReal) (half_pos hε), hrec ε (b t.toNNReal) hε]
  · rfl
  · rfl

/-- The field-averaged stopped annular horizon increment is measurable. -/
theorem measurable_annular_exit_horizon_increment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (γ α δ : ℝ) {D : Set ℂ} (hD : IsOpen D) (N : ℕ) :
    Measurable (annularExitHorizonIncrement P hcirc γ α δ ε D N) := by
  have := hh.isProbabilityMeasure
  obtain ⟨F, hFm, hFae⟩ := exists_measurable_annular_exit_horizon_sample hh hε γ α δ hD N
  have hm : Measurable (fun b => ∫ ω, |F (b,ω)| ∂P) :=
    (hFm.abs.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  convert hm using 1
  funext b
  unfold annularExitHorizonIncrement
  apply integral_congr_ae
  filter_upwards [hFae] with ω hω
  rw [hω b]

/-- Finite-horizon annular increments satisfy a linear-in-horizon rate bound. -/
theorem brownian_annular_exit_horizon_increment_annealed_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ (x : ℂ) (N : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1/2 → ε ≤ δ →
        Integrable (annularExitHorizonIncrement P hcirc γ α δ ε D N) (planarBrownianMotion x) ∧
        (∫ b, annularExitHorizonIncrement P hcirc γ α δ ε D N b ∂planarBrownianMotion x) ≤
        (N : ℝ) * (((Real.exp (γ^2*Real.log 2)-1) *
          (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))) := by
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_annular_exit_block_increment_annealed_le hh hγ0 hγ2 α hδ hD hDb
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro x N ε hε hεhalf hεδ
  let F := annularExitHorizonIncrement P hcirc γ α δ ε D N
  let B : ℕ → ContinuousPath ℂ → ℝ := fun k => annularExitBlockIncrement P hcirc γ α δ ε D k
  have hB : ∀ k, Integrable (B k) (planarBrownianMotion x) := fun k =>
    (hb x k ε hε hεhalf hεδ).1
  have hS : Integrable (fun b => ∑ k ∈ Finset.range N, B k b) (planarBrownianMotion x) :=
    integrable_finsetSum _ (fun k hk => hB k)
  have hm : Measurable F := measurable_annular_exit_horizon_increment hh hε γ α δ hD N
  have hF0 : ∀ b, 0 ≤ F b := by
    intro b
    apply integral_nonneg
    intro ω
    exact abs_nonneg _
  have hle : ∀ᵐ b ∂planarBrownianMotion x, F b ≤ ∑ k ∈ Finset.range N, B k b := by
    filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top x hDb] with b hfin
    exact annular_exit_horizon_increment_le_sum_blocks hh hε hεhalf hεδ γ α D N b hfin.ne
  have hi : Integrable F (planarBrownianMotion x) := by
    apply hS.mono' hm.aestronglyMeasurable
    filter_upwards [hle] with b h
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 b)] using h
  refine ⟨hi, (integral_mono_ae hi hS hle).trans ?_⟩
  rw [integral_finsetSum _ (fun k hk => hB k)]
  calc
    _ ≤ ∑ k ∈ Finset.range N, (((Real.exp (γ^2*Real.log 2)-1) *
          (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact (hb x k ε hε hεhalf hεδ).2
    _ = _ := by simp [mul_add]

private theorem summable_nat_mul_exp_log_dyadicScale {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℕ => (k : ℝ) * Real.exp (Real.log (dyadicScale k) * c)) := by
  change Summable (fun k : ℕ => (k : ℝ) * Real.exp (Real.log (LatticeProb.LQG.dyadicScale k) * c))
  simp_rw [LatticeProb.Gauss.exp_log_dyadicScale_mul]
  have hq : ‖Real.exp (Real.log 2⁻¹ * c)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (Real.exp_lt_exp.mpr (mul_neg_of_neg_of_pos (Real.log_neg (by norm_num) (by norm_num)) hc)).trans_eq Real.exp_zero
  simpa only [pow_one] using (summable_pow_mul_geometric_of_norm_lt_one 1 hq)

/-- Annealed annular horizon increments are summable at dyadic scales. -/
theorem summable_brownian_annular_exit_horizon_increment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) :
    Summable (fun k : ℕ => ∫ b, annularExitHorizonIncrement P hcirc γ α δ
      (dyadicScale k) D k b ∂planarBrownianMotion x) := by
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_annular_exit_horizon_increment_annealed_le hh hγ0 hγ2 α hδ hD hDb
  let A : ℝ := ((Real.exp (γ^2*Real.log 2)-1) *
    (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2
  let c : ℝ := (d-γ^2+(2*γ-θ)^2/2)/2
  let e : ℝ := (θ-γ)^2/2
  have hc : 0 < c := by dsimp [c]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hsum : Summable (fun k : ℕ => (k : ℝ) *
      (A * Real.exp (Real.log (dyadicScale k) * c) +
      2*M*Real.exp (Real.log (dyadicScale k) * e))) := by
    have h1 := (summable_nat_mul_exp_log_dyadicScale hc).mul_left A
    have h2 := (summable_nat_mul_exp_log_dyadicScale he).mul_left (2*M)
    apply (h1.add h2).congr
    intro k
    ring
  have hlim : Tendsto dyadicScale atTop (𝓝 0) := by
    unfold dyadicScale
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev : ∀ᶠ k in atTop, dyadicScale k < min (1/2) δ :=
    hlim.eventually (Iio_mem_nhds (lt_min (by norm_num) hδ))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  apply (summable_nat_add_iff N).1
  apply Summable.of_nonneg_of_le
    (fun k => integral_nonneg (fun b => integral_nonneg (fun ω => abs_nonneg _)))
    _ ((summable_nat_add_iff N).2 hsum)
  intro k
  have hk := hN (k + N) (by omega)
  exact (hb x (k+N) _ (dyadicScale_pos _)
    (le_of_lt (lt_of_lt_of_le hk (min_le_left _ _)))
    (le_of_lt (lt_of_lt_of_le hk (min_le_right _ _)))).2

/-- A stopped finite-horizon annular increment is integrable over the field. -/
theorem integrable_annular_exit_horizon_sample_field {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε δ : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hεδ : ε ≤ δ)
    (γ α : ℝ) (D : Set ℂ) (N : ℕ) (b : ContinuousPath ℂ)
    (hfin : ContinuousPath.exitTime D b ≠ ⊤) :
    Integrable (fun ω => ∫ t in (0 : ℝ)..min (N : ℝ) (ContinuousPath.exitTime D b).toReal,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
        ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
          (b t.toNNReal)) P := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  let G : Ω → ℂ → ℝ := fun ω z =>
    (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
    ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)
  let F : Ω → ℝ := fun ω => ∫ t in (0 : ℝ)..min (N : ℝ) (ContinuousPath.exitTime D b).toReal,
    A.indicator (G ω) (b t.toNNReal)
  let B : ℕ → Ω → ℝ := fun k ω => ∫ t in Ioc (k : ℝ)
      (min ((k : ℝ) + 1) (ContinuousPath.exitTime D b).toReal), A.indicator (G ω) (b t.toNNReal)
  have hB : ∀ k, Integrable (B k) P := by
    intro k
    exact integrable_annular_exit_block_increment_field hh hε hεhalf hεδ γ α D k b hfin
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  have hsum : F =ᵐ[P] fun ω => ∑ k ∈ Finset.range N, B k ω := by
    filter_upwards [hcont, ae_recentered_inserted_circle_average hh α] with ω hcont hrec
    have hc (r : ℝ) (hr : 0 < r) : Continuous (fun z =>
        r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)) := by
      have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) =
          fun z => hcirc ω r z - hcirc ω 1 0 - α * Real.log (max r ‖z‖) := by
        funext z
        exact (hrec r z hr).symm
      have hc' : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) := by
        rw [heq]
        exact ((hcont r hr).sub continuous_const).sub (continuous_const.mul
          ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hr).ne')))
      exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc'))
    have hG : Continuous (G ω) := (hc (ε/2) (half_pos hε)).sub (hc ε hε)
    have hint := intervalIntegrable_annular_density (G ω) hG δ b 0
      (ContinuousPath.exitTime D b).toReal
    exact intervalIntegral_stopped_eq_sum_blocks _ _ ENNReal.toReal_nonneg N hint
  have hsumint : Integrable (fun ω => ∑ k ∈ Finset.range N, B k ω) P := by
    exact integrable_finsetSum _ (fun k hk => hB k)
  have hF : Integrable F P := hsumint.congr hsum.symm
  exact hF

/-- For a finite-exit path, the full annular increment is field integrable. -/
theorem integrable_annular_exit_sample_field {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε δ : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hεδ : ε ≤ δ)
    (γ α : ℝ) (D : Set ℂ) (b : ContinuousPath ℂ)
    (hfin : ContinuousPath.exitTime D b ≠ ⊤) :
    Integrable (fun ω => ∫ t in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
        ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
          (b t.toNNReal)) P := by
  obtain ⟨N, hN⟩ := exists_nat_ge (ContinuousPath.exitTime D b).toReal
  have h := integrable_annular_exit_horizon_sample_field hh hε hεhalf hεδ γ α D N b hfin
  rwa [min_eq_right hN] at h

/-- The actual-exit annular increment has a jointly measurable version. -/
theorem exists_measurable_annular_exit_sample {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (γ α δ : ℝ) {D : Set ℂ} (hD : IsOpen D) :
    ∃ F : ContinuousPath ℂ × Ω → ℝ, Measurable F ∧ ∀ᵐ ω ∂P, ∀ b,
      F (b,ω) = ∫ t in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
            (b t.toNNReal) := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let J : Ω × ℂ → ℝ := fun q => A.indicator (fun z =>
    (ε/2)^(γ^2/2) * Real.exp (γ*(H q.1 (ε/2) z-H q.1 1 0 - α*Real.log (max (ε/2) ‖z‖))) -
    ε^(γ^2/2) * Real.exp (γ*(H q.1 ε z-H q.1 1 0 - α*Real.log (max ε ‖z‖)))) q.2
  have h1 : Measurable (fun q : Ω × ℂ => H q.1 (ε/2) q.2) :=
    (hHm (ε/2) (half_pos hε)).comp measurable_swap
  have h2 : Measurable (fun q : Ω × ℂ => H q.1 ε q.2) := (hHm ε hε).comp measurable_swap
  have h3 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
    (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
  have hJ : Measurable J := by
    apply Measurable.indicator _ (hA.preimage measurable_snd)
    exact (measurable_const.mul (measurable_const.mul ((h1.sub h3).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp).sub
      (measurable_const.mul (measurable_const.mul ((h2.sub h3).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp)
  let U : ContinuousPath ℂ → ℝ := fun b => (ContinuousPath.exitTime D b).toReal
  have hU : Measurable U := (ContinuousPath.measurable_exitTime D hD).ennreal_toReal
  have heval : Measurable (fun q : (ContinuousPath ℂ × Ω) × ℝ => q.1.1 q.2.toNNReal) := by
    exact (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk (measurable_fst.comp measurable_fst))
  let S : Set ((ContinuousPath ℂ × Ω) × ℝ) := {q | 0 < q.2 ∧ q.2 ≤ U q.1.1}
  have hS : MeasurableSet S := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (hU.comp (measurable_fst.comp measurable_fst)))
  let Q : (ContinuousPath ℂ × Ω) × ℝ → ℝ := fun q =>
    S.indicator (fun q => J (q.1.2, q.1.1 q.2.toNNReal)) q
  have hQ : Measurable Q := by
    exact (hJ.comp ((measurable_snd.comp measurable_fst).prodMk heval)).indicator hS
  refine ⟨fun q => ∫ t, Q (q,t), hQ.stronglyMeasurable.integral_prod_right'.measurable, ?_⟩
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec b
  have hU0 : 0 ≤ U b := ENNReal.toReal_nonneg
  rw [intervalIntegral.integral_of_le hU0, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Q, S, U, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Ioc, J, A]
  split_ifs with ht hz
  · rw [hω (ε/2) (b t.toNNReal), hω ε (b t.toNNReal), hω 1 0,
      hrec (ε/2) (b t.toNNReal) (half_pos hε), hrec ε (b t.toNNReal) hε]
  · rfl
  · rfl

/-- The norm of a signed stopped integral is bounded by its horizon and positive tails. -/
theorem enorm_intervalIntegral_sub_le_horizon_add_tails (p q : ℝ → ℝ) (hp : Measurable p)
    (hp0 : ∀ t, 0 ≤ p t) (hq0 : ∀ t, 0 ≤ q t) (T τ : ℝ)
    (hT : 0 ≤ T) (hτ : 0 ≤ τ)
    (hpi : IntervalIntegrable p volume 0 τ) (hqi : IntervalIntegrable q volume 0 τ) :
    ‖∫ t in (0 : ℝ)..τ, (p t - q t)‖ₑ ≤
      ‖∫ t in (0 : ℝ)..min T τ, (p t - q t)‖ₑ +
      (∫⁻ t in Ioc T τ, ENNReal.ofReal (p t)) +
      ∫⁻ t in Ioc T τ, ENNReal.ofReal (q t) := by
  by_cases h : τ ≤ T
  · rw [min_eq_right h]
    exact le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ _ from bot_le))
      (le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ _ from bot_le))
  · have hTτ : T ≤ τ := (lt_of_not_ge h).le
    rw [min_eq_left hTτ]
    have hi : IntervalIntegrable (fun t => p t - q t) volume 0 τ := hpi.sub hqi
    have hi1 : IntervalIntegrable (fun t => p t - q t) volume 0 T := by
      apply hi.mono_set
      rw [uIcc_of_le hT, uIcc_of_le hτ]
      exact Icc_subset_Icc le_rfl hTτ
    have hi2 : IntervalIntegrable (fun t => p t - q t) volume T τ := by
      apply hi.mono_set
      rw [uIcc_of_le hTτ, uIcc_of_le hτ]
      exact Icc_subset_Icc hT le_rfl
    have heq := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    rw [← heq]
    have htail : ‖∫ t in T..τ, (p t - q t)‖ₑ ≤
        (∫⁻ t in Ioc T τ, ENNReal.ofReal (p t)) +
        ∫⁻ t in Ioc T τ, ENNReal.ofReal (q t) := by
      rw [intervalIntegral.integral_of_le hTτ]
      calc
        _ ≤ ∫⁻ t in Ioc T τ, ‖p t - q t‖ₑ := enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ t in Ioc T τ, ENNReal.ofReal (p t) + ENNReal.ofReal (q t) := by
          apply lintegral_mono
          intro t
          change ‖p t - q t‖ₑ ≤ ENNReal.ofReal (p t) + ENNReal.ofReal (q t)
          rw [Real.enorm_eq_ofReal_abs]
          calc
            _ ≤ ENNReal.ofReal (p t + q t) := ENNReal.ofReal_le_ofReal (by
              calc
                |p t - q t| ≤ |p t| + |q t| := abs_sub _ _
                _ = p t + q t := by rw [abs_of_nonneg (hp0 t), abs_of_nonneg (hq0 t)])
            _ = _ := ENNReal.ofReal_add (hp0 t) (hq0 t)
        _ = _ := lintegral_add_left hp.ennreal_ofReal _

    exact (enorm_add_le _ _).trans (by
      simpa only [add_assoc, add_comm, add_left_comm] using
        add_le_add_left htail ‖∫ t in (0 : ℝ)..T, (p t - q t)‖ₑ)

/-- Actual annular exit increments are bounded by the horizon increment and two tails. -/
theorem ae_annular_exit_increment_le_horizon_add_tails {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (γ α δ : ℝ) (D : Set ℂ) :
    ∀ᵐ ω ∂P, ∀ (b : ContinuousPath ℂ) (T : ℝ), 0 ≤ T →
      ‖∫ t in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
            (b t.toNNReal)‖ₑ ≤
      ‖∫ t in (0 : ℝ)..min T (ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
            (b t.toNNReal)‖ₑ +
      (∫⁻ t in Ioc T (ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z => ENNReal.ofReal (
          (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z)))
            (b t.toNNReal)) +
      ∫⁻ t in Ioc T (ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z => ENNReal.ofReal (
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)))
            (b t.toNNReal) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  filter_upwards [hcont, ae_recentered_inserted_circle_average hh α] with ω hcont hrec b T hT
  let Z : ℝ → ℂ → ℝ := fun r z => r^(γ^2/2) *
    Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)
  have hc (r : ℝ) (hr : 0 < r) : Continuous (Z r) := by
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) =
        fun z => hcirc ω r z - hcirc ω 1 0 - α * Real.log (max r ‖z‖) := by
      funext z
      exact (hrec r z hr).symm
    have hc' : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) := by
      rw [heq]
      exact ((hcont r hr).sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hr).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc'))
  let p : ℝ → ℝ := fun t => A.indicator (Z (ε/2)) (b t.toNNReal)
  let q : ℝ → ℝ := fun t => A.indicator (Z ε) (b t.toNNReal)
  have hp : Measurable p := ((hc (ε/2) (half_pos hε)).measurable.indicator hA).comp
    (b.continuous.measurable.comp measurable_real_toNNReal)
  have hp0 : ∀ t, 0 ≤ p t := by
    intro t
    simp only [p, Set.indicator_apply]
    split_ifs <;> positivity
  have hq0 : ∀ t, 0 ≤ q t := by
    intro t
    simp only [q, Set.indicator_apply]
    split_ifs <;> positivity
  have hpi : IntervalIntegrable p volume 0 (ContinuousPath.exitTime D b).toReal :=
    intervalIntegrable_annular_density (Z (ε/2)) (hc (ε/2) (half_pos hε)) δ b 0 _
  have hqi : IntervalIntegrable q volume 0 (ContinuousPath.exitTime D b).toReal :=
    intervalIntegrable_annular_density (Z ε) (hc ε hε) δ b 0 _
  have h := enorm_intervalIntegral_sub_le_horizon_add_tails p q hp hp0 hq0 T _ hT
    ENNReal.toReal_nonneg hpi hqi
  have hsub (t : ℝ) : A.indicator (fun z => Z (ε/2) z - Z ε z) (b t.toNNReal) = p t - q t := by
    simp only [p, q, Set.indicator_apply]
    split_ifs <;> simp
  have hoff (r t : ℝ) : A.indicator (fun z => ENNReal.ofReal (Z r z)) (b t.toNNReal) =
      ENNReal.ofReal (A.indicator (Z r) (b t.toNNReal)) := by
    simp only [Set.indicator_apply]
    split_ifs <;> simp
  change ‖∫ t in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal,
      A.indicator (fun z => Z (ε/2) z - Z ε z) (b t.toNNReal)‖ₑ ≤
    ‖∫ t in (0 : ℝ)..min T (ContinuousPath.exitTime D b).toReal,
      A.indicator (fun z => Z (ε/2) z - Z ε z) (b t.toNNReal)‖ₑ +
    (∫⁻ t in Ioc T (ContinuousPath.exitTime D b).toReal,
      A.indicator (fun z => ENNReal.ofReal (Z (ε/2) z)) (b t.toNNReal)) +
    ∫⁻ t in Ioc T (ContinuousPath.exitTime D b).toReal,
      A.indicator (fun z => ENNReal.ofReal (Z ε z)) (b t.toNNReal)
  simp_rw [hsub, hoff]
  exact h

/-- Positive annular clock tails have a jointly measurable field-path version. -/
theorem exists_measurable_annular_exit_positive_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (γ α δ : ℝ) {D : Set ℂ} (hD : IsOpen D) (T : ℝ) :
    ∃ F : ContinuousPath ℂ × Ω → ℝ≥0∞, Measurable F ∧ ∀ᵐ ω ∂P, ∀ b,
      F (b,ω) = ∫⁻ t in Ioc T (ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z => ENNReal.ofReal (
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)))
            (b t.toNNReal) := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let J : Ω × ℂ → ℝ≥0∞ := fun q => A.indicator (fun z => ENNReal.ofReal (
    ε^(γ^2/2) * Real.exp (γ*(H q.1 ε z-H q.1 1 0 - α*Real.log (max ε ‖z‖))))) q.2
  have h1 : Measurable (fun q : Ω × ℂ => H q.1 ε q.2) := (hHm ε hε).comp measurable_swap
  have h2 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
    (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
  have hJ : Measurable J := by
    apply Measurable.indicator _ (hA.preimage measurable_snd)
    exact (measurable_const.mul (measurable_const.mul ((h1.sub h2).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp).ennreal_ofReal
  let U : ContinuousPath ℂ → ℝ := fun b => (ContinuousPath.exitTime D b).toReal
  have hU : Measurable U := (ContinuousPath.measurable_exitTime D hD).ennreal_toReal
  have heval : Measurable (fun q : (ContinuousPath ℂ × Ω) × ℝ => q.1.1 q.2.toNNReal) := by
    exact (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk (measurable_fst.comp measurable_fst))
  let S : Set ((ContinuousPath ℂ × Ω) × ℝ) := {q | T < q.2 ∧ q.2 ≤ U q.1.1}
  have hS : MeasurableSet S := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (hU.comp (measurable_fst.comp measurable_fst)))
  let Q : (ContinuousPath ℂ × Ω) × ℝ → ℝ≥0∞ := fun q =>
    S.indicator (fun q => J (q.1.2, q.1.1 q.2.toNNReal)) q
  have hQ : Measurable Q := by
    exact (hJ.comp ((measurable_snd.comp measurable_fst).prodMk heval)).indicator hS
  refine ⟨fun q => ∫⁻ t, Q (q,t), Measurable.lintegral_prod_right hQ, ?_⟩
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec b
  rw [← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro t
  simp only [Q, S, U, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Ioc, J, A]
  split_ifs
  · rw [hω ε (b t.toNNReal), hω 1 0, hrec ε (b t.toNNReal) hε]
  · rfl
  · rfl

/-- The annealed exit increment is bounded by the horizon estimate and two tails. -/
theorem exists_annular_exit_sample_annealed_le_horizon_add_tails {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) {δ ε : ℝ} (hδ : 0 < δ)
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hεδ : ε ≤ δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) (x : ℂ) (N : ℕ) :
    ∃ F : ContinuousPath ℂ × Ω → ℝ, Measurable F ∧
      (∀ᵐ ω ∂P, ∀ b, F (b,ω) = ∫ t in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
            (b t.toNNReal)) ∧
      (∫⁻ b, ∫⁻ ω, ‖F (b,ω)‖ₑ ∂P ∂planarBrownianMotion x) ≤
        ENNReal.ofReal (∫ b, annularExitHorizonIncrement P hcirc γ α δ ε D N b ∂planarBrownianMotion x) +
        (∫⁻ b, ∫⁻ ω, ∫⁻ t in Ioc (N : ℝ) (ContinuousPath.exitTime D b).toReal,
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z => ENNReal.ofReal (
            (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z)))
              (b t.toNNReal) ∂volume ∂P ∂planarBrownianMotion x) +
        ∫⁻ b, ∫⁻ ω, ∫⁻ t in Ioc (N : ℝ) (ContinuousPath.exitTime D b).toReal,
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z => ENNReal.ofReal (
            ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)))
              (b t.toNNReal) ∂volume ∂P ∂planarBrownianMotion x := by
  have := hh.isProbabilityMeasure
  obtain ⟨F, hFm, hFae⟩ := exists_measurable_annular_exit_sample hh hε γ α δ hD
  obtain ⟨G, hGm, hGae⟩ := exists_measurable_annular_exit_horizon_sample hh hε γ α δ hD N
  obtain ⟨U, hUm, hUae⟩ := exists_measurable_annular_exit_positive_tail hh (half_pos hε) γ α δ hD N
  obtain ⟨V, hVm, hVae⟩ := exists_measurable_annular_exit_positive_tail hh hε γ α δ hD N
  refine ⟨F, hFm, hFae, ?_⟩
  have hpoint : ∀ b, ∀ᵐ ω ∂P, ‖F (b,ω)‖ₑ ≤ ‖G (b,ω)‖ₑ + U (b,ω) + V (b,ω) := by
    intro b
    filter_upwards [hFae, hGae, hUae, hVae,
      ae_annular_exit_increment_le_horizon_add_tails hh hε γ α δ D] with ω hf hg hu hv hs
    rw [hf b, hg b, hu b, hv b]
    exact hs b N (Nat.cast_nonneg N)
  have hGnonneg : Measurable (fun q : ContinuousPath ℂ × Ω => ‖G q‖ₑ) := hGm.enorm
  have hGint : Measurable (fun b => ∫⁻ ω, ‖G (b,ω)‖ₑ ∂P) :=
    Measurable.lintegral_prod_right hGnonneg
  have hUint : Measurable (fun b => ∫⁻ ω, U (b,ω) ∂P) := Measurable.lintegral_prod_right hUm
  have hVint : Measurable (fun b => ∫⁻ ω, V (b,ω) ∂P) := Measurable.lintegral_prod_right hVm
  have hbase : (∫⁻ b, ∫⁻ ω, ‖F (b,ω)‖ₑ ∂P ∂planarBrownianMotion x) ≤
      (∫⁻ b, ∫⁻ ω, ‖G (b,ω)‖ₑ ∂P ∂planarBrownianMotion x) +
      (∫⁻ b, ∫⁻ ω, U (b,ω) ∂P ∂planarBrownianMotion x) +
      ∫⁻ b, ∫⁻ ω, V (b,ω) ∂P ∂planarBrownianMotion x := by
    calc
      _ ≤ ∫⁻ b, ((∫⁻ ω, ‖G (b,ω)‖ₑ ∂P) + (∫⁻ ω, U (b,ω) ∂P)) +
          ∫⁻ ω, V (b,ω) ∂P ∂planarBrownianMotion x := by
        apply lintegral_mono
        intro b
        calc
          _ ≤ ∫⁻ ω, (‖G (b,ω)‖ₑ + U (b,ω)) + V (b,ω) ∂P := lintegral_mono_ae (hpoint b)
          _ = _ := by
            have hg : Measurable (fun ω => ‖G (b,ω)‖ₑ) :=
              hGnonneg.comp (measurable_const.prodMk measurable_id)
            have hu : Measurable (fun ω => U (b,ω)) :=
              hUm.comp (measurable_const.prodMk measurable_id)
            change (∫⁻ ω, ((fun ω => ‖G (b,ω)‖ₑ) + (fun ω => U (b,ω))) ω + V (b,ω) ∂P) = _
            rw [lintegral_add_left (hg.add hu)]
            change (∫⁻ ω, ‖G (b,ω)‖ₑ + U (b,ω) ∂P) + _ = _
            rw [lintegral_add_left hg]
      _ = _ := by
        change (∫⁻ b, ((fun b => ∫⁻ ω, ‖G (b,ω)‖ₑ ∂P) +
          (fun b => ∫⁻ ω, U (b,ω) ∂P)) b + (∫⁻ ω, V (b,ω) ∂P)
            ∂planarBrownianMotion x) = _
        rw [lintegral_add_left (hGint.add hUint)]
        change (∫⁻ b, (∫⁻ ω, ‖G (b,ω)‖ₑ ∂P) +
          (∫⁻ ω, U (b,ω) ∂P) ∂planarBrownianMotion x) + _ = _
        rw [lintegral_add_left hGint]
  have htailU : (∫⁻ b, ∫⁻ ω, U (b,ω) ∂P ∂planarBrownianMotion x) =
      ∫⁻ b, ∫⁻ ω, ∫⁻ t in Ioc (N : ℝ) (ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z => ENNReal.ofReal (
          (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z)))
            (b t.toNNReal) ∂volume ∂P ∂planarBrownianMotion x := by
    apply lintegral_congr
    intro b
    apply lintegral_congr_ae
    filter_upwards [hUae] with ω hω
    exact hω b
  have htailV : (∫⁻ b, ∫⁻ ω, V (b,ω) ∂P ∂planarBrownianMotion x) =
      ∫⁻ b, ∫⁻ ω, ∫⁻ t in Ioc (N : ℝ) (ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z => ENNReal.ofReal (
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)))
            (b t.toNNReal) ∂volume ∂P ∂planarBrownianMotion x := by
    apply lintegral_congr
    intro b
    apply lintegral_congr_ae
    filter_upwards [hVae] with ω hω
    exact hω b
  have hGreal : (∫⁻ b, ∫⁻ ω, ‖G (b,ω)‖ₑ ∂P ∂planarBrownianMotion x) =
      ENNReal.ofReal (∫ b, annularExitHorizonIncrement P hcirc γ α δ ε D N b ∂planarBrownianMotion x) := by
    obtain ⟨θ, d, M, h1, h2, h3, h4, h5, h6, hb⟩ :=
      brownian_annular_exit_horizon_increment_annealed_le hh hγ0 hγ2 α hδ hD hDb
    rw [ofReal_integral_eq_lintegral_ofReal (hb x N ε hε hεhalf hεδ).1]
    · apply lintegral_congr_ae
      filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top x hDb] with b hfin
      have hi := integrable_annular_exit_horizon_sample_field hh hε hεhalf hεδ γ α D N b hfin.ne
      rw [show annularExitHorizonIncrement P hcirc γ α δ ε D N b =
        ∫ ω, ‖G (b,ω)‖ ∂P from by
          unfold annularExitHorizonIncrement
          apply integral_congr_ae
          filter_upwards [hGae] with ω hω
          rw [hω b, Real.norm_eq_abs]]
      have hGi : Integrable (fun ω => G (b,ω)) P := hi.congr (by
        filter_upwards [hGae] with ω hω
        exact (hω b).symm)
      exact (ofReal_integral_norm_eq_lintegral_enorm hGi).symm
    · filter_upwards with b
      apply integral_nonneg
      intro ω
      exact abs_nonneg _
  rwa [hGreal, htailU, htailV] at hbase


/-- Both positive exit tails have finite sums along a common dyadic tail. -/
theorem exists_summable_dyadic_annular_exit_tails {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {D : Set ℂ}
    (hD : IsOpen D) (hDb : Bornology.IsBounded D) {δ : ℝ} (hδ : 0 < δ)
    (γ α : ℝ) (x : ℂ) :
    ∃ N : ℕ, (∀ k : ℕ, dyadicScale (k+N) ≤ δ ∧ dyadicScale (k+N) ≤ 1/2) ∧
      (∑' k : ℕ, ∫⁻ b, ∫⁻ ω, ∫⁻ t in Ioc ((k+N : ℕ) : ℝ) (ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => ENNReal.ofReal (((dyadicScale (k+N))/2) ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ((dyadicScale (k+N))/2) z))) (b t.toNNReal)
        ∂volume ∂P ∂planarBrownianMotion x) < ⊤ ∧
      (∑' k : ℕ, ∫⁻ b, ∫⁻ ω, ∫⁻ t in Ioc ((k+N : ℕ) : ℝ) (ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => ENNReal.ofReal ((dyadicScale (k+N)) ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (k+N)) z))) (b t.toNNReal)
        ∂volume ∂P ∂planarBrownianMotion x) < ⊤ := by
  have hlim : Tendsto dyadicScale atTop (𝓝 0) := by
    unfold dyadicScale
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually
    (Iio_mem_nhds (lt_min (by norm_num : (0 : ℝ) < 1/2) hδ)))
  have hsmall (n : ℕ) : 0 < dyadicScale (max n N) ∧
      dyadicScale (max n N) ≤ δ ∧ dyadicScale (max n N) ≤ 1/2 := by
    have h := hN (max n N) (le_max_right _ _)
    exact ⟨dyadicScale_pos _, (lt_of_lt_of_le h (min_le_right _ _)).le,
      (lt_of_lt_of_le h (min_le_left _ _)).le⟩
  have ha := tsum_annular_exit_time_tails_lt_top hh hD hDb hδ γ α x
    (fun n => dyadicScale (max n N) / 2) (by
      intro n
      have h := hsmall n
      exact ⟨half_pos h.1, (half_le_self h.1.le).trans h.2.1,
        (half_le_self h.1.le).trans h.2.2⟩)
  have hb := tsum_annular_exit_time_tails_lt_top hh hD hDb hδ γ α x
    (fun n => dyadicScale (max n N)) hsmall
  have hi : Function.Injective (fun k : ℕ => k + N) := by
    intro a b h
    exact Nat.add_right_cancel h
  have ha' := ENNReal.tsum_comp_le_tsum_of_injective hi (fun n : ℕ =>
    ∫⁻ b, ∫⁻ ω, ∫⁻ t in Ioc (n : ℝ) (ContinuousPath.exitTime D b).toReal,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator
      (fun z => ENNReal.ofReal ((dyadicScale (max n N) / 2) ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (max n N) / 2) z)))
          (b t.toNNReal) ∂volume ∂P ∂planarBrownianMotion x)
  have hb' := ENNReal.tsum_comp_le_tsum_of_injective hi (fun n : ℕ =>
    ∫⁻ b, ∫⁻ ω, ∫⁻ t in Ioc (n : ℝ) (ContinuousPath.exitTime D b).toReal,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator
      (fun z => ENNReal.ofReal ((dyadicScale (max n N)) ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (max n N)) z)))
          (b t.toNNReal) ∂volume ∂P ∂planarBrownianMotion x)
  refine ⟨N, ?_, ?_, ?_⟩
  · intro k
    have h := hsmall (k + N)
    simpa only [max_eq_left (Nat.le_add_left N k)] using h.2
  · simpa only [Function.comp_apply, max_eq_left (Nat.le_add_left N _)] using ha'.trans_lt ha
  · simpa only [Function.comp_apply, max_eq_left (Nat.le_add_left N _)] using hb'.trans_lt hb

end HarmonicBalls
