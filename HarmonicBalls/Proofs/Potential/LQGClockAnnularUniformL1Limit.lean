import HarmonicBalls.Proofs.Potential.LQGClockAnnularExitL1Limit
import HarmonicBalls.Proofs.Potential.LQGClockAnnularStoppedUniformLimit

/-! # Integrable bounds for annular clocks

The annular clocks at actual Brownian exit admit an integrable bound uniform in scale.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Filter Set HarmonicBalls.Section6
open scoped NNReal ENNReal Topology ZeroAtInfty

namespace HarmonicBalls

/-- The actual annular clocks at exit have a common integrable Brownian bound. -/
theorem ae_exists_integrable_bound_annular_clock_exit {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) :
    ∀ᵐ ω ∂P, ∃ G : ContinuousPath ℂ → ℝ,
      Integrable G (planarBrownianMotion x) ∧
      ∀ᵐ b ∂planarBrownianMotion x, ∀ k : ℕ,
        |∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal,
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            (dyadicScale k)^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z))
            (b s.toNNReal)| ≤ G b := by
  obtain ⟨N, hsum⟩ := ae_summable_brownian_annular_exit_increments hh hγ0 hγ2 α x hδ hD hDb
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  filter_upwards [hsum, hcont, ae_recentered_inserted_circle_average hh α,
    ae_integrable_annular_clock_exit hh hD hDb γ α δ x] with ω hsum hcont hrec hint
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  let Z : ℕ → ℂ → ℝ := fun k z => (dyadicScale k)^(γ^2/2) *
    Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z)
  let Y : ℕ → ContinuousPath ℂ → ℝ := fun k b =>
    ∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, A.indicator (Z k) (b s.toNNReal)
  have hc (k : ℕ) : Continuous (Z k) := by
    have hr := dyadicScale_pos k
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) =
        fun z => hcirc ω (dyadicScale k) z - hcirc ω 1 0 - α * Real.log (max (dyadicScale k) ‖z‖) := by
      funext z
      exact (hrec _ z hr).symm
    have hc' : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) := by
      rw [heq]
      exact ((hcont _ hr).sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hr).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc'))
  have hYi : ∀ k, Integrable (Y k) (planarBrownianMotion x) := hint
  have hs : Summable (fun k => ∫ b, |Y (k+1) b - Y k b| ∂planarBrownianMotion x) := by
    let f : ℕ → ℝ := fun k => ∫ b, ‖∫ t in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal,
        A.indicator (fun z => (dyadicScale k / 2)^(γ^2/2) *
          Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k / 2) z) -
          (dyadicScale k)^(γ^2/2) *
          Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z))
          (b t.toNNReal)‖ ∂planarBrownianMotion x
    change Summable (fun k => f (k+N)) at hsum
    have hs' : Summable f := (summable_nat_add_iff N).1 hsum
    apply hs'.congr
    intro k
    apply integral_congr_ae
    filter_upwards with b
    have hscale : dyadicScale (k+1) = dyadicScale k / 2 := by
      simp only [dyadicScale, pow_succ]
      ring
    have hi1 := intervalIntegrable_annular_density (Z (k+1)) (hc (k+1)) δ b 0 (ContinuousPath.exitTime D b).toReal
    have hi0 := intervalIntegrable_annular_density (Z k) (hc k) δ b 0 (ContinuousPath.exitTime D b).toReal
    change ‖_‖ = |Y (k+1) b - Y k b|
    rw [← Real.norm_eq_abs, show Y (k+1) b - Y k b = _ from (intervalIntegral.integral_sub hi1 hi0).symm]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [A, Z, Set.indicator_apply]
    split_ifs <;> simp [hscale]
  obtain ⟨G, hG, hbound⟩ :=
    LatticeProb.Prob.exists_integrable_dominating_of_summable hYi (by
      simpa only [Real.norm_eq_abs] using hs)
  refine ⟨G, hG, ?_⟩
  filter_upwards [ae_all_iff.mpr hbound] with b hb k
  simpa only [Real.norm_eq_abs, Y, A, Z] using hb k

/-- Actual annular clocks stopped at exit have a common integrable bound at every time. -/
theorem ae_exists_integrable_bound_stopped_annular_clock {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) :
    ∀ᵐ ω ∂P, ∃ G : ContinuousPath ℂ → ℝ,
      Integrable G (planarBrownianMotion x) ∧
      ∀ᵐ b ∂planarBrownianMotion x, ∀ (k : ℕ) (t : ℝ≥0),
        |∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            (dyadicScale k)^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z))
            (b s.toNNReal)| ≤ G b := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  filter_upwards [ae_exists_integrable_bound_annular_clock_exit hh hγ0 hγ2 α x hδ hD hDb,
    hcont, ae_recentered_inserted_circle_average hh α] with ω hbound hcont hrec
  obtain ⟨G, hG, hbound⟩ := hbound
  refine ⟨G, hG, ?_⟩
  filter_upwards [hbound] with b hb k t
  let Z : ℂ → ℝ := fun z => (dyadicScale k)^(γ^2/2) *
    Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z)
  let g : ℝ → ℝ := fun s => {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator Z (b s.toNNReal)
  have hr := dyadicScale_pos k
  have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) =
      fun z => hcirc ω (dyadicScale k) z - hcirc ω 1 0 - α * Real.log (max (dyadicScale k) ‖z‖) := by
    funext z
    exact (hrec _ z hr).symm
  have hc : Continuous Z := by
    have hc' : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) := by
      rw [heq]
      exact ((hcont _ hr).sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hr).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc'))
  have hg0 (s : ℝ) : 0 ≤ g s := by
    apply Set.indicator_nonneg
    intro z hz
    exact mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le
  have htau : 0 ≤ (ContinuousPath.exitTime D b).toReal := ENNReal.toReal_nonneg
  have hmin : 0 ≤ min (t : ℝ) (ContinuousPath.exitTime D b).toReal := le_min t.coe_nonneg htau
  have hi := intervalIntegrable_annular_density Z hc δ b 0 (ContinuousPath.exitTime D b).toReal
  have hle : (∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal, g s) ≤
      ∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, g s :=
    intervalIntegral.integral_mono_interval le_rfl hmin (min_le_right _ _)
      (Eventually.of_forall hg0) hi
  have h0 : 0 ≤ ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal, g s :=
    intervalIntegral.integral_nonneg_of_forall hmin hg0
  change |∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal, g s| ≤ G b
  rw [abs_of_nonneg h0]
  exact hle.trans ((le_abs_self _).trans (hb k))

/-- A stopped annular time integral is measurable as a function of the path. -/
theorem measurable_stopped_annular_time_integral {D : Set ℂ} (hD : IsOpen D)
    (f : ℂ → ℝ) (hf : Continuous f) (δ : ℝ) (t : ℝ≥0) :
    Measurable (fun b : ContinuousPath ℂ =>
      ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal)) := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let g : ℂ → ℝ := A.indicator f
  have hg : Measurable g := hf.measurable.indicator hA
  let τ : ContinuousPath ℂ → ℝ := fun b => min (t : ℝ) (ContinuousPath.exitTime D b).toReal
  have hτ : Measurable τ := measurable_const.min
    (ENNReal.measurable_toReal.comp (ContinuousPath.measurable_exitTime D hD))
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
    rw [intervalIntegral.integral_of_le (le_min t.coe_nonneg ENNReal.toReal_nonneg)]
    change (∫ s in Set.Ioc 0 (τ b), g (b s.toNNReal)) = _
    rw [← integral_indicator measurableSet_Ioc]
    rfl
  exact hI.measurable

/-- A common integrable bound upgrades almost-sure uniform convergence to convergence
of the expected uniform distance. -/
theorem tendsto_integral_uniform_distance_of_dominated {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {T : ℝ≥0}
    (A : ℕ → X → C(Icc (0 : ℝ) (T : ℝ), ℝ))
    (hA : ∀ k, Measurable (A k)) (G : X → ℝ) (hG : Integrable G μ)
    (hbound : ∀ᵐ x ∂μ, ∀ k, ‖A k x‖ ≤ G x)
    (hconv : ∀ᵐ x ∂μ, ∃ F, Tendsto (fun k => A k x) atTop (𝓝 F)) :
    ∃ F : X → C(Icc (0 : ℝ) (T : ℝ), ℝ),
      Measurable F ∧
      (∀ᵐ x ∂μ, Tendsto (fun k => A k x) atTop (𝓝 (F x))) ∧
      (∀ k, Integrable (fun x => ‖A k x - F x‖) μ) ∧
      Tendsto (fun k => ∫ x, ‖A k x - F x‖ ∂μ) atTop (𝓝 0) := by
  let F : X → C(Icc (0 : ℝ) (T : ℝ), ℝ) := fun x => limUnder atTop (fun k => A k x)
  have hFm : Measurable F :=
    (StronglyMeasurable.limUnder (fun k => (hA k).stronglyMeasurable)).measurable
  have hF : ∀ᵐ x ∂μ, Tendsto (fun k => A k x) atTop (𝓝 (F x)) := by
    filter_upwards [hconv] with x hx
    exact tendsto_nhds_limUnder hx
  have hFbound : ∀ᵐ x ∂μ, ‖F x‖ ≤ G x := by
    filter_upwards [hbound, hF] with x hx hlim
    exact le_of_tendsto (continuous_norm.continuousAt.tendsto.comp hlim)
      (Eventually.of_forall hx)
  have he : ∀ k, AEStronglyMeasurable (fun x => ‖A k x - F x‖) μ :=
    fun k => (((hA k).sub hFm).norm).aestronglyMeasurable
  have hb : ∀ k, ∀ᵐ x ∂μ, ‖‖A k x - F x‖‖ ≤ (2 : ℝ) * G x := by
    intro k
    filter_upwards [hbound, hFbound] with x hx hy
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    calc
      ‖A k x - F x‖ ≤ ‖A k x‖ + ‖F x‖ := norm_sub_le _ _
      _ ≤ G x + G x := add_le_add (hx k) hy
      _ = 2 * G x := by ring
  have hi (k : ℕ) : Integrable (fun x => ‖A k x - F x‖) μ :=
    (hG.const_mul 2).mono' (he k) (hb k)
  have ht : ∀ᵐ x ∂μ, Tendsto (fun k => ‖A k x - F x‖) atTop (𝓝 0) := by
    filter_upwards [hF] with x hx
    have hs : Tendsto (fun k => A k x - F x) atTop (𝓝 (0 : C(Icc (0 : ℝ) (T : ℝ), ℝ))) := by
      simpa using hx.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => F x) atTop (𝓝 (F x)))
    have hn : Continuous (fun y : C(Icc (0 : ℝ) (T : ℝ), ℝ) => ‖y‖) := continuous_norm
    convert hn.continuousAt.tendsto.comp hs using 1
    · rfl
    · simp
  refine ⟨F, hFm, hF, hi, ?_⟩
  simpa using tendsto_integral_of_dominated_convergence (fun x => 2 * G x)
    he (hG.const_mul 2) hb ht

/-- At each fixed start and finite horizon, the actual stopped annular clocks converge in
Brownian L¹ for the uniform norm, for almost every field. -/
theorem ae_exists_stopped_annular_clock_uniform_L1_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ (A : ℕ → ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ))
        (F : ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ)),
      (∀ k b t, A k b t = ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (dyadicScale k)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z))
          (b s.toNNReal)) ∧
      Measurable F ∧
      (∀ᵐ b ∂planarBrownianMotion x, Tendsto (fun k => A k b) atTop (𝓝 (F b))) ∧
      (∀ k, Integrable (fun b => ‖A k b - F b‖) (planarBrownianMotion x)) ∧
      Tendsto (fun k => ∫ b, ‖A k b - F b‖ ∂planarBrownianMotion x) atTop (𝓝 0) := by
  have hγlt : γ < 2 := by nlinarith [sq_nonneg (γ - 1)]
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  filter_upwards [ae_exists_integrable_bound_stopped_annular_clock hh hγ0 hγlt α x hδ hD hDb,
    ae_field_ae_path_exists_locally_uniform_limit_annularClock_stopped hh x hγ0 hγ2 α hδ hDb,
    hcont, ae_recentered_inserted_circle_average hh α] with ω hbound hconv hcont hrec
  let Z : ℕ → ℂ → ℝ := fun k z => (dyadicScale k)^(γ^2/2) *
    Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z)
  have hc (k : ℕ) : Continuous (Z k) := by
    have hr := dyadicScale_pos k
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) =
        fun z => hcirc ω (dyadicScale k) z - hcirc ω 1 0 - α * Real.log (max (dyadicScale k) ‖z‖) := by
      funext z
      exact (hrec _ z hr).symm
    have hc' : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) := by
      rw [heq]
      exact ((hcont _ hr).sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hr).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc'))
  let A : ℕ → ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ) := fun k b =>
    ⟨fun t => ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (Z k) (b s.toNNReal),
      (intervalIntegral.continuous_primitive
        (fun a c => intervalIntegrable_annular_density (Z k) (hc k) δ b a c) 0).comp
          (continuous_subtype_val.min continuous_const)⟩
  have hAm (k : ℕ) : Measurable (A k) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    simpa only [A, ContinuousMap.coe_mk, Real.toNNReal_of_nonneg t.property.1, NNReal.coe_mk] using
      measurable_stopped_annular_time_integral hD (Z k) (hc k) δ ((t : ℝ).toNNReal)
  obtain ⟨G, hG, hbound⟩ := hbound
  have hAb : ∀ᵐ b ∂planarBrownianMotion x, ∀ k, ‖A k b‖ ≤ G b := by
    filter_upwards [hbound] with b hb k
    have hG0 : 0 ≤ G b := (abs_nonneg _).trans (hb 0 0)
    apply (ContinuousMap.norm_le (A k b) hG0).2
    intro t
    simpa only [A, ContinuousMap.coe_mk, Real.norm_eq_abs,
      Real.toNNReal_of_nonneg t.property.1, NNReal.coe_mk] using hb k ((t : ℝ).toNNReal)
  have hAc : ∀ᵐ b ∂planarBrownianMotion x, ∃ F, Tendsto (fun k => A k b) atTop (𝓝 F) := by
    filter_upwards [hconv] with b hb
    obtain ⟨_, F, hFc, _, _, hF⟩ := hb
    let B : C(Icc (0 : ℝ) (T : ℝ), ℝ) :=
      ⟨fun t => F ((t : ℝ).toNNReal), hFc.comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩
    refine ⟨B, Metric.tendsto_nhds.mpr ?_⟩
    intro ε hε
    filter_upwards [hF T (ε / 2) (half_pos hε)] with k hk
    have hle : ‖A k b - B‖ ≤ ε / 2 := by
      apply (ContinuousMap.norm_le (A k b - B) (le_of_lt (half_pos hε))).2
      intro t
      have ht : (t : ℝ).toNNReal ≤ T := by
        exact NNReal.coe_le_coe.mp (by simpa [Real.toNNReal_of_nonneg t.property.1] using t.property.2)
      have hx := (hk ((t : ℝ).toNNReal) ht).le
      simpa only [A, B, ContinuousMap.sub_apply, ContinuousMap.coe_mk, Real.norm_eq_abs,
        Real.toNNReal_of_nonneg t.property.1, NNReal.coe_mk] using hx
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hle (half_lt_self hε)
  obtain ⟨F, hFm, hFlim, hFi, hL1⟩ :=
    tendsto_integral_uniform_distance_of_dominated A hAm G hG hAb hAc
  exact ⟨A, F, fun _ _ _ => rfl, hFm, hFlim, hFi, hL1⟩

end HarmonicBalls
