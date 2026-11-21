import HarmonicBalls.Proofs.Potential.LQGClockInnerUncappedExpectation
import HarmonicBalls.Proofs.Potential.LQGClockHalfDiscMeasurableLimit
import HarmonicBalls.Proofs.Potential.LQGClockExteriorExhaustion

/-! # Half-disc clocks for positive insertions with `γ ^ 2 / 2 < 2 - γ * α`

The expected inner occupations vanish uniformly over dyadic smoothing scales and unit times
whenever `0 < γ * α` and `γ ^ 2 / 2 < 2 - γ * α`. Since these occupations decrease as the inner
cutoff shrinks, they also vanish almost surely. Consequently the dyadic half-disc clocks of
the inserted field converge locally uniformly in time, with a jointly measurable limit, for
`γ ^ 2 < 2` in this range, which contains the range `γ ^ 2 / 2 < 2 * (2 - γ * α) / (2 + γ * α)`
of the earlier pathwise statements. With limits of the exterior clocks, the inserted field
has an LQG clock for almost every field in the same range.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- The actual inner occupations vanish uniformly over all dyadic smoothing scales and unit
times, almost surely under the product law, whenever `γ ^ 2 / 2 < 2 - γ * α`. -/
theorem ae_prod_tendsto_iSup_time_inner_inserted_zero_of_lt_two_sub
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hγ : 0 < γ) (hsub : γ ^ 2 / 2 < 2 - γ*α) :
    ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      Tendsto (fun n : ℕ => ⨆ i : ℕ, ⨆ t : Icc (0 : ℝ) 1,
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (i+1)
        ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator
            (fun z => ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal)))
        atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let X (n : ℕ) (q : Ω × ContinuousPath ℂ) : ℝ≥0∞ := ⨆ i : ℕ, ⨆ t : Icc (0 : ℝ) 1,
    let ε : ℝ := (2 : ℝ)⁻¹ ^ (i+1)
    ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
      ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => ε^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal))
  have hδ (n : ℕ) : (2 : ℝ)⁻¹ ^ (n+2) ≤ 1/2 := by
    rw [show n+2 = (n+1)+1 by omega, pow_succ]
    have h : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hX (n : ℕ) : AEMeasurable (X n) (P.prod (planarBrownianMotion x)) := by
    have heq : X n = fun q => ⨆ i : ℕ,
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (i+1)
        ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+2)}.indicator
            (fun z => ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal)) := by
      funext q
      apply iSup_congr
      intro i
      have hset : {z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2} =
          {z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+2)} := by
        ext z
        simp only [mem_ofPred_eq]
        exact ⟨And.left, fun hz => ⟨hz, (le_of_lt hz).trans (hδ n)⟩⟩
      simp only [hset]
      apply le_antisymm
      · apply iSup_le
        intro t
        exact lintegral_mono_set (Ioc_subset_Ioc le_rfl t.2.2)
      · exact le_iSup_of_le ⟨1, by simp⟩ le_rfl
    rw [heq]
    apply AEMeasurable.iSup
    intro i
    exact aemeasurable_inner_inserted_clock_cell hh (planarBrownianMotion x)
      (by positivity) γ α _ 0 1
  have hanti (q : Ω × ContinuousPath ℂ) : Antitone (fun n => X n q) := by
    intro n m hnm
    apply iSup_mono
    intro i
    apply iSup_mono
    intro t
    apply lintegral_mono
    intro s
    apply ENNReal.ofReal_le_ofReal
    apply Set.indicator_le_indicator_of_subset _ (fun z => mul_nonneg
      (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le)
    intro z hz
    exact ⟨lt_of_lt_of_le hz.1 (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)), hz.2⟩
  have hE := tendsto_lintegral_iSup_time_inner_inserted_zero_of_lt_two_sub hh x hq0 hγ hsub
  let Y : Ω × ContinuousPath ℂ → ℝ≥0∞ := fun q => ⨅ n, X n q
  have hYm : AEMeasurable Y (P.prod (planarBrownianMotion x)) := AEMeasurable.iInf hX
  have hY0 : (∫⁻ q, Y q ∂(P.prod (planarBrownianMotion x))) = 0 := by
    apply le_antisymm _ zero_le
    exact ge_of_tendsto' hE (fun n => lintegral_mono (fun q => iInf_le (fun n => X n q) n))
  have hYae := (lintegral_eq_zero_iff' hYm).mp hY0
  filter_upwards [hYae] with q hq
  have h := tendsto_atTop_iInf (hanti q)
  have hq' : (⨅ n, X n q) = 0 := hq
  rw [hq'] at h
  exact h

/-- The actual dyadic half-disc clocks converge uniformly on the unit time
interval for each fixed Brownian start, in the stated parameter range. -/
theorem ae_prod_exists_uniform_limit_halfDiscClock_of_lt_two_sub
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hγ : 0 < γ) (hγ2 : γ^2 < 2)
    (hsub : γ ^ 2 / 2 < 2 - γ*α) :
    ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∃ F : Icc (0 : ℝ) 1 → ℝ, TendstoUniformly
        (fun i (t : Icc (0 : ℝ) 1) =>
          stoppedAnnularClock (fun z => (dyadicScale (i+1))^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (i+1)) z)) 0
              (fun _ => t.1.toNNReal) q.2) F atTop := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let δ : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n+2)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hann (n : ℕ) : ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∃ F : Icc (0 : ℝ) 1 → ℝ, TendstoUniformly
        (fun i (t : Icc (0 : ℝ) 1) =>
          stoppedAnnularClock (fun z => (dyadicScale (i+1))^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (i+1)) z)) (δ n)
              (fun _ => t.1.toNNReal) q.2) F atTop := by
    obtain ⟨K, hK⟩ := exists_ae_uniform_limit_stoppedAnnularClock hh x hγ hγ2 α (hδ n)
    filter_upwards [hK] with q hq
    obtain ⟨F, hF⟩ := hq
    refine ⟨F, ?_⟩
    rw [Metric.tendstoUniformly_iff]
    intro η hη
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hF η hη)
    filter_upwards [eventually_ge_atTop (N+K)] with i hi t
    have hk : K ≤ i+1 := by omega
    have hj : N ≤ i+1-K := by omega
    have h := hN (i+1-K) hj t
    have heq : i+1-K+K = i+1 := Nat.sub_add_cancel hk
    rw [heq] at h
    simpa [Real.dist_eq, abs_sub_comm] using h
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  let hf := Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)
  filter_upwards [ae_all_iff.mpr hann,
    ae_prod_tendsto_iSup_time_inner_inserted_zero_of_lt_two_sub hh x hq0 hγ hsub,
    hf.ae hcont, hf.ae (ae_recentered_inserted_circle_average hh α)] with q hq hsmall hc hr
  let D : ℕ → ℂ → ℝ := fun i z => (dyadicScale (i+1))^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (i+1)) z)
  have hD (i : ℕ) : Continuous (D i) := by
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (i+1)) z) =
        fun z => hcirc q.1 (dyadicScale (i+1)) z - hcirc q.1 1 0 - α * Real.log (max (dyadicScale (i+1)) ‖z‖) := by
      funext z
      exact (hr (dyadicScale (i+1)) z (dyadicScale_pos _)).symm
    have hcircins : Continuous
        (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (i+1)) z) := by
      rw [heq]
      exact ((hc _ (dyadicScale_pos _)).sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left (dyadicScale_pos _)).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hcircins))
  have hD0 (i : ℕ) (z : ℂ) : 0 ≤ D i z :=
    mul_nonneg (Real.rpow_nonneg (dyadicScale_pos _).le _) (Real.exp_pos _).le
  let e : ℕ → ℝ≥0∞ := fun n => ⨆ i : ℕ, ⨆ t : Icc (0 : ℝ) 1,
    ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
      ({z : ℂ | ‖z‖ < δ n ∧ ‖z‖ ≤ 1/2}.indicator (D i) (q.2 s.toNNReal))
  apply exists_tendstoUniformly_of_ennreal_cutoff_approximations
    (B := fun n i t => stoppedAnnularClock (D i) (δ n) (fun _ => t.1.toNNReal) q.2) (e := e)
  · exact hq
  · simpa [e, D, δ, dyadicScale] using hsmall
  · intro n i t
    rw [ofReal_dist_halfDisc_annularClock_eq_inner q.2 (D i) (hD i) (hD0 i) (δ n) t]
    exact (le_iSup (fun t : Icc (0 : ℝ) 1 => ∫⁻ s in Ioc (0 : ℝ) t.1,
      ENNReal.ofReal ({z : ℂ | ‖z‖ < δ n ∧ ‖z‖ ≤ 1/2}.indicator (D i) (q.2 s.toNNReal))) t).trans
      (le_iSup (fun i : ℕ => ⨆ t : Icc (0 : ℝ) 1, ∫⁻ s in Ioc (0 : ℝ) t.1,
        ENNReal.ofReal ({z : ℂ | ‖z‖ < δ n ∧ ‖z‖ ≤ 1/2}.indicator (D i) (q.2 s.toNNReal))) i)

/-- For each fixed start, the half-disc convergence also holds for almost every
field and then almost every Brownian path. -/
theorem ae_field_ae_exists_uniform_limit_halfDiscClock_of_lt_two_sub
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hγ : 0 < γ) (hγ2 : γ^2 < 2)
    (hsub : γ ^ 2 / 2 < 2 - γ*α) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x,
      ∃ F : Icc (0 : ℝ) 1 → ℝ, TendstoUniformly
        (fun i (t : Icc (0 : ℝ) 1) =>
          stoppedAnnularClock (fun z => (dyadicScale (i+1))^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (i+1)) z)) 0
              (fun _ => t.1.toNNReal) b) F atTop :=
  Measure.ae_ae_of_ae_prod
    (ae_prod_exists_uniform_limit_halfDiscClock_of_lt_two_sub hh x hq0 hγ hγ2 hsub)

/-- The half-disc limit has continuous, nonnegative and nondecreasing paths. -/
theorem ae_prod_exists_regular_uniform_limit_halfDiscClock_of_lt_two_sub
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hγ : 0 < γ) (hγ2 : γ^2 < 2)
    (hsub : γ ^ 2 / 2 < 2 - γ*α) :
    ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∃ F : Icc (0 : ℝ) 1 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        TendstoUniformly
          (fun i (t : Icc (0 : ℝ) 1) =>
            stoppedAnnularClock (fun z => (dyadicScale (i+1))^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (i+1)) z)) 0
                (fun _ => t.1.toNNReal) q.2) F atTop := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let hf := Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)
  filter_upwards [ae_prod_exists_uniform_limit_halfDiscClock_of_lt_two_sub hh x hq0 hγ hγ2 hsub,
    hf.ae (ae_continuous_stoppedAnnularClock_time hh γ α 0),
    hf.ae (ae_dyadic_stoppedAnnularClock_monotone_and_cell hh γ α 0)] with q hq hc hm
  obtain ⟨F, hF⟩ := hq
  have hF' : ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop, ∀ t,
      |stoppedAnnularClock (fun z => (dyadicScale (i+1))^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (i+1)) z)) 0
          (fun _ => t.1.toNNReal) q.2 - F t| < η := by
    intro η hη
    filter_upwards [(Metric.tendstoUniformly_iff.mp hF) η hη] with i hi t
    simpa [Real.dist_eq, abs_sub_comm] using hi t
  obtain ⟨hFc, hF0, hFm⟩ := continuous_nonneg_monotone_of_uniform_limit
    (A := fun i (t : Icc (0 : ℝ) 1) => stoppedAnnularClock (fun z =>
      (dyadicScale (i+1))^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (i+1)) z)) 0
          (fun _ => t.1.toNNReal) q.2) (F := F)
    (fun i => (hc (i+1) q.2).comp continuous_subtype_val)
    (fun i t => stoppedAnnularClock_nonneg _ (fun z => mul_nonneg
      (Real.rpow_nonneg (dyadicScale_pos (i+1)).le _) (Real.exp_pos _).le) _ _ _)
    (fun i s t hst => (hm (i+1) q.2).1 s.2 t.2 hst) hF'
  exact ⟨F, hFc, hF0, hFm, hF⟩

/-- Half-disc convergence holds simultaneously after all integer time shifts. -/
theorem ae_exists_uniform_limit_integer_shift_halfDiscClock_of_lt_two_sub
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hγ : 0 < γ) (hγ2 : γ^2 < 2)
    (hsub : γ ^ 2 / 2 < 2 - γ*α) :
    ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∀ n : ℕ, ∃ F : Icc (0 : ℝ) 1 → ℝ,
        ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : Icc (0 : ℝ) 1,
          |stoppedAnnularClock (fun z => (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z)) 0
              (fun _ => ((t : ℝ).toNNReal)) (ContinuousPath.shift n p.2) - F t| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨M, hMm, hMc, hMae⟩ := exists_measurable_stoppedAnnularClock_time hh γ α 0
  let A (j : ℕ) (p : Ω × ContinuousPath ℂ) : C(Icc (0 : ℝ) 1, ℝ) :=
    ⟨fun t => M (j+1) (p, t), hMc (j+1) p⟩
  have hAm (j : ℕ) : Measurable (A j) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (hMm (j+1)).comp (measurable_id.prodMk measurable_const)
  let S : Set (Ω × ContinuousPath ℂ) := {p | ∃ F, Tendsto (fun j => A j p) atTop (𝓝 F)}
  have hSm : MeasurableSet S := measurableSet_exists_tendsto hAm
  have hS (y : ℂ) : ∀ᵐ p ∂(P.prod (planarBrownianMotion y)), p ∈ S := by
    filter_upwards [ae_prod_exists_regular_uniform_limit_halfDiscClock_of_lt_two_sub hh y hq0 hγ hγ2 hsub,
      (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion y)).ae hMae] with p hp hM
    obtain ⟨F, hFc, _, _, hF⟩ := hp
    let G : C(Icc (0 : ℝ) 1, ℝ) := ⟨F, hFc⟩
    refine ⟨G, ?_⟩
    apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
    rw [Metric.tendstoUniformly_iff] at hF ⊢
    intro η hη
    filter_upwards [hF η hη] with j hj t
    change dist (F t) (M (j+1) (p, t)) < η
    rw [hM (j+1) p.2 t]
    exact hj t
  apply ae_all_iff.mpr
  intro n
  have hshift := ae_prod_planarBrownianMotion_shift_of_forall_ae P x n S hSm hS
  filter_upwards [hshift, (Measure.quasiMeasurePreserving_fst
    (μ := P) (ν := planarBrownianMotion x)).ae hMae] with p hp hM
  obtain ⟨F, hF⟩ := hp
  refine ⟨F, ?_⟩
  have hu := ContinuousMap.tendsto_iff_tendstoUniformly.mp hF
  rw [Metric.tendstoUniformly_iff] at hu
  intro η hη
  filter_upwards [hu η hη] with j hj t
  have heq := hM (j+1) (ContinuousPath.shift n p.2) t
  change |stoppedAnnularClock _ _ _ _ - F t| < η
  rw [← heq, ← Real.dist_eq, dist_comm]
  exact hj t

/-- At each start, the dyadic half-disc clocks converge locally uniformly in time. -/
theorem ae_exists_locally_uniform_limit_halfDiscClock_of_lt_two_sub
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hγ : 0 < γ) (hγ2 : γ^2 < 2)
    (hsub : γ ^ 2 / 2 < 2 - γ*α) :
    ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ),
            {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                  (p.2 s.toNNReal)) - F t| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hdensity : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (fun z =>
      (dyadicScale (k+1))^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (k+1)) z)) := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec k
    have hc : Continuous (hcirc ω (dyadicScale (k+1))) := by
      rw [← funext (hω (dyadicScale (k+1)))]
      exact hHc ω (dyadicScale (k+1)) (dyadicScale_pos (k+1))
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (k+1)) z) =
        fun z => hcirc ω (dyadicScale (k+1)) z - hcirc ω 1 0 - α * Real.log (max (dyadicScale (k+1)) ‖z‖) := by
      funext z
      exact (hrec _ z (dyadicScale_pos (k+1))).symm
    have hci : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (k+1)) z) := by
      rw [heq]
      exact (hc.sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log
          (fun _ => (lt_max_of_lt_left (dyadicScale_pos (k+1))).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hci))
  filter_upwards [ae_exists_uniform_limit_integer_shift_halfDiscClock_of_lt_two_sub hh x hq0 hγ hγ2 hsub,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hdensity] with p hp hc
  let f (j : ℕ) : ℂ → ℝ := fun z => (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z)
  let g (j : ℕ) (t : ℝ) : ℝ :=
    {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (f j) (p.2 t.toNNReal)
  let A (j : ℕ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, g j s
  have hblock : ∀ n : ℕ, ∃ F : Icc (0 : ℝ) 1 → ℝ,
      ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ u : Icc (0 : ℝ) 1,
        |(A j ((n : ℝ) + u) - A j n) - F u| < η := by
    intro n
    obtain ⟨F, hF⟩ := hp n
    refine ⟨F, fun η hη => ?_⟩
    filter_upwards [hF η hη] with j hj u
    have heq := stoppedAnnularClock_shift_eq_time_increment (f j) (hc j) 0 p.2 n u
    change stoppedAnnularClock (f j) 0 _ _ = A j (n + u) - A j n at heq
    rw [← heq]
    exact hj u
  have hnat := exists_uniform_limit_on_nat_intervals_of_unit_blocks A
    (fun j => intervalIntegral.integral_same) hblock
  let B (j : ℕ) (t : ℝ≥0) := A j t
  have hBc (j : ℕ) : Continuous (B j) := by
    have h := intervalIntegral.continuous_primitive
      (fun a b => intervalIntegrable_annular_density (f j) (hc j) 0 p.2 a b) 0
    exact h.comp continuous_subtype_val
  have hf0 (j : ℕ) (z : ℂ) : 0 ≤ f j z :=
    mul_nonneg (Real.rpow_nonneg (dyadicScale_pos (j+1)).le _) (Real.exp_pos _).le
  have hg0 (j : ℕ) (t : ℝ) : 0 ≤ g j t :=
    Set.indicator_nonneg (fun z _ => hf0 j z) _
  have hB0 (j : ℕ) (t : ℝ≥0) : 0 ≤ B j t :=
    intervalIntegral.integral_nonneg_of_forall t.coe_nonneg (hg0 j)
  have hBm (j : ℕ) : Monotone (B j) := by
    intro s t hst
    exact intervalIntegral.integral_mono_interval le_rfl s.coe_nonneg hst
      (Eventually.of_forall (hg0 j))
      (intervalIntegrable_annular_density (f j) (hc j) 0 p.2 0 t)
  have hnatB (N : ℕ) : ∃ G : ℝ≥0 → ℝ, ∀ η : ℝ, 0 < η →
      ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ N → |B j t - G t| < η := by
    obtain ⟨G, hG⟩ := hnat N
    refine ⟨fun t => G t, fun η hη => ?_⟩
    filter_upwards [hG η hη] with j hj t ht
    exact hj t ⟨t.coe_nonneg, by exact_mod_cast ht⟩
  exact exists_continuous_monotone_limit_of_uniform_on_nat_intervals B hBc hB0 hBm hnatB

/-- At each fixed start, the half-disc clock limit has a jointly measurable
field, path and time representative with regular time paths. -/
theorem exists_measurable_locally_uniform_limit_halfDiscClock_of_lt_two_sub
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hγ : 0 < γ) (hγ2 : γ^2 < 2)
    (hsub : γ ^ 2 / 2 < 2 - γ*α) :
    ∃ F : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable F ∧
      (∀ p, Continuous (fun t => F (p,t)) ∧ (∀ t, 0 ≤ F (p,t)) ∧
        Monotone (fun t => F (p,t))) ∧
      ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
        ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ),
            {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                  (p.2 s.toNNReal)) - F (p,t)| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, hHc, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let B : Set ℂ := {z | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hB : MeasurableSet B := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let Z (j : ℕ) (ω : Ω) (z : ℂ) : ℝ := (dyadicScale (j+1))^(γ^2/2) *
    Real.exp (γ * (H ω (dyadicScale (j+1)) z - α * Real.log (max (dyadicScale (j+1)) ‖z‖)))
  have hZm (j : ℕ) : Measurable (fun p : Ω × ℂ => Z j p.1 p.2) := by
    have he : Measurable (fun p : Ω × ℂ => H p.1 (dyadicScale (j+1)) p.2) :=
      (hHm _ (dyadicScale_pos (j+1))).comp measurable_swap
    exact measurable_const.mul (measurable_const.mul (he.sub (measurable_const.mul
      ((measurable_const.max measurable_snd.norm).log)))).exp
  let A (j : ℕ) (p : (Ω × ContinuousPath ℂ) × ℝ≥0) : ℝ :=
    ∫ s in (0 : ℝ)..(p.2 : ℝ), B.indicator (Z j p.1.1) (p.1.2 s.toNNReal)
  have hAm (j : ℕ) : Measurable (A j) := by
    have hev : Measurable (fun p : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ =>
        p.1.1.2 p.2.toNNReal) :=
      (continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable.comp
        (measurable_fst.fst.snd.prodMk measurable_snd)
    have hI : Measurable (fun p : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ =>
        B.indicator (Z j p.1.1.1) (p.1.1.2 p.2.toNNReal)) := by
      convert (hZm j).comp (measurable_fst.fst.fst.prodMk hev) |>.indicator
        (hev hB) using 1
      ext p
      rfl
    have hS : MeasurableSet {p : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ |
        0 < p.2 ∧ p.2 ≤ (p.1.2 : ℝ)} :=
      (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_coe_nnreal_real.comp measurable_fst.snd))
    have h := (hI.indicator hS).stronglyMeasurable.integral_prod_right' (ν := volume)
    convert h.measurable using 1
    ext p
    dsimp only [A]
    rw [intervalIntegral.integral_of_le p.2.coe_nonneg, ← integral_indicator measurableSet_Ioc]
    rfl
  have hAe : ∀ᵐ ω ∂P, ∀ j b t,
      A j ((ω,b),t) = ∫ s in (0 : ℝ)..(t : ℝ), B.indicator (fun z =>
        (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (j+1)) z))
            (b s.toNNReal) := by
    filter_upwards [hHae] with ω hω j b t
    apply intervalIntegral.integral_congr
    intro s hs
    apply congrArg (fun f : ℂ → ℝ => B.indicator f (b s.toNNReal))
    funext z
    have he : H ω (dyadicScale (j+1)) z = hcirc ω (dyadicScale (j+1)) z := hω _ _
    have hl : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z (dyadicScale (j+1)) =
        Real.log (max (dyadicScale (j+1)) ‖z‖) := by
      simpa using LatticeProb.Gauss.circleAverage_log_norm_sub_eq z 0 (dyadicScale_pos (j+1))
    simp only [Z, LatticeProb.Gauss.fieldCircleAverage, hl, he]
  have hconv : ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∃ G : ℝ≥0 → ℝ,
      Continuous G ∧ (∀ t, 0 ≤ G t) ∧ Monotone G ∧
      ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
        |A j (p,t) - G t| < η := by
    filter_upwards [ae_exists_locally_uniform_limit_halfDiscClock_of_lt_two_sub hh x hq0 hγ hγ2 hsub,
      (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hAe]
      with p hp he
    obtain ⟨G, hGc, hG0, hGm, hG⟩ := hp
    refine ⟨G, hGc, hG0, hGm, ?_⟩
    intro T η hη
    filter_upwards [hG T η hη] with j hj t ht
    rw [he j p.2 t]
    exact hj t ht
  obtain ⟨F, hFm, hFr, hF⟩ :=
    exists_measurable_locally_uniform_limit (P.prod (planarBrownianMotion x)) A hAm hconv
  refine ⟨F, hFm, hFr, ?_⟩
  filter_upwards [hF, (Measure.quasiMeasurePreserving_fst
    (μ := P) (ν := planarBrownianMotion x)).ae hAe] with p hp he
  intro T η hη
  filter_upwards [hp T η hη] with j hj t ht
  have h := hj t ht
  rw [he j p.2 t] at h
  exact h

/-- For a positive insertion with `γ ^ 2 < 2` and `γ ^ 2 / 2 < 2 - γ * α`, locally uniform limits
of the exterior clocks stopped at the exit of the balls of integer radius give an LQG clock of
the inserted field for almost every field. -/
theorem exists_ae_isLQGClock_fieldCircleAverage_of_stopped_exterior_of_lt_two_sub
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hγ : 0 < γ) (hγ2 : γ^2 < 2) (hsub : γ ^ 2 / 2 < 2 - γ*α)
    (hstop : ∀ N : ℕ, ∃ G : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable G ∧
      ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
        ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..min (t : ℝ)
            (ContinuousPath.exitTime (Metric.ball (0 : ℂ) ((N : ℝ) + 1)) p.2).toReal,
            {z : ℂ | 1/2 < ‖z‖}.indicator (fun z =>
              (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                  (p.2 s.toNNReal)) - G (p,t)| < η) :
    ∃ F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ, ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) x (F ω) := by
  obtain ⟨F, hFm, -, hF⟩ :=
    exists_measurable_locally_uniform_limit_halfDiscClock_of_lt_two_sub hh x hq0 hγ hγ2 hsub
  obtain ⟨G, hGm, hG⟩ := exists_ae_eventually_uniform_of_stopped_balls x (fun j p u =>
      ∫ s in (0 : ℝ)..u, {z : ℂ | 1/2 < ‖z‖}.indicator (fun z =>
        (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
            (p.2 s.toNNReal)) hstop
  exact ⟨_, ae_isLQGClock_fieldCircleAverage_of_halfDisc_exterior hh x F G hFm hGm hF hG⟩

end HarmonicBalls
