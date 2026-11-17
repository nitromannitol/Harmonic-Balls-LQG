import HarmonicBalls.Proofs.Potential.LQGClockCutoffGluing

/-! # Uniform convergence of half-disc clocks

Annular convergence and vanishing inner occupations yield convergence on the
half unit disc for nonpositive insertions.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- Nonpositive insertions have vanishing inner occupation uniformly in scale and time. -/
theorem ae_prod_tendsto_iSup_time_inner_nonpositive_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (hα : α ≤ 0) :
    ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      Tendsto (fun n : ℕ => ⨆ i : ℕ, ⨆ t : Icc (0 : ℝ) 1,
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (i+1)
        ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator
            (fun z => ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) (p.2 s.toNNReal)))
        atTop (𝓝 0) := by
  let q : ℝ := (2 - γ^2) / 4
  let β : ℝ := q / γ
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hqhalf : q ≤ 1/2 := by dsimp [q]; nlinarith [sq_nonneg γ]
  have hβ : 0 < β := div_pos hq0 hγ
  have hqeq : γ * β = q := by dsimp [β]; field_simp
  have hq2 : γ * β < 2 := by rw [hqeq]; linarith
  have hsub : γ^2 / 2 < 2 * (2-γ*β) / (2+γ*β) := by
    rw [hqeq]
    have hden : 0 < 2 + q := by linarith
    have hbound : (1 : ℝ) ≤ 2 * (2-q) / (2+q) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    linarith
  filter_upwards [ae_prod_tendsto_iSup_time_inner_inserted_zero hh x
    (by rw [hqeq]; exact hq0) hq2 hγ hsub] with p hp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hp
  · intro n; exact zero_le
  · intro n
    apply iSup_le; intro i
    apply iSup_le; intro t
    refine (lintegral_mono ?_).trans (le_iSup_of_le i (le_iSup_of_le t le_rfl))
    intro s
    apply ENNReal.ofReal_le_ofReal
    simp only [Set.indicator_apply]
    split_ifs with hz
    · have hε : 0 < (2 : ℝ)⁻¹ ^ (i+1) := by positivity
      have hεhalf : (2 : ℝ)⁻¹ ^ (i+1) ≤ 1/2 := by
        rw [pow_succ]
        have hh : (2 : ℝ)⁻¹ ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        nlinarith
      have hlog : Real.circleAverage (fun y : ℂ => Real.log ‖y‖)
          (p.2 s.toNNReal) ((2 : ℝ)⁻¹ ^ (i+1)) =
          Real.log (max ((2 : ℝ)⁻¹ ^ (i+1)) ‖p.2 s.toNNReal‖) := by
        simpa using (LatticeProb.Gauss.circleAverage_log_norm_sub_eq
          (p.2 s.toNNReal) 0 hε)
      have hlogle : Real.log (max ((2 : ℝ)⁻¹ ^ (i+1)) ‖p.2 s.toNNReal‖) ≤ 0 :=
        Real.log_nonpos (le_of_lt (lt_max_of_lt_left hε)) (max_le (by linarith) (by linarith [hz.2]))
      have hcomp : LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1)
          ((2 : ℝ)⁻¹ ^ (i+1)) (p.2 s.toNNReal) ≤
          LatticeProb.Gauss.fieldCircleAverage β (hcirc p.1)
          ((2 : ℝ)⁻¹ ^ (i+1)) (p.2 s.toNNReal) := by
        have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hα.trans hβ.le)) hlogle
        dsimp [LatticeProb.Gauss.fieldCircleAverage]
        rw [hlog]
        linarith
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hcomp hγ.le)) (Real.rpow_nonneg hε.le _)
    · exact le_rfl


/-- The actual dyadic half-disc clocks converge uniformly on the unit time
interval for each fixed Brownian start, in the stated parameter range. -/
theorem ae_prod_exists_uniform_limit_nonpositive_halfDiscClock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (hα : α ≤ 0) :
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
    ae_prod_tendsto_iSup_time_inner_nonpositive_zero hh x hγ hγ2 hα,
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
theorem ae_field_ae_exists_uniform_limit_nonpositive_halfDiscClock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (hα : α ≤ 0) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x,
      ∃ F : Icc (0 : ℝ) 1 → ℝ, TendstoUniformly
        (fun i (t : Icc (0 : ℝ) 1) =>
          stoppedAnnularClock (fun z => (dyadicScale (i+1))^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (i+1)) z)) 0
              (fun _ => t.1.toNNReal) b) F atTop :=
  Measure.ae_ae_of_ae_prod
    (ae_prod_exists_uniform_limit_nonpositive_halfDiscClock hh x hγ hγ2 hα)


/-- The half-disc limit has continuous, nonnegative and nondecreasing paths. -/
theorem ae_prod_exists_regular_uniform_limit_nonpositive_halfDiscClock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (hα : α ≤ 0) :
    ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∃ F : Icc (0 : ℝ) 1 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        TendstoUniformly
          (fun i (t : Icc (0 : ℝ) 1) =>
            stoppedAnnularClock (fun z => (dyadicScale (i+1))^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (i+1)) z)) 0
                (fun _ => t.1.toNNReal) q.2) F atTop := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let hf := Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)
  filter_upwards [ae_prod_exists_uniform_limit_nonpositive_halfDiscClock hh x hγ hγ2 hα,
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

/-- For each fixed start, the regular limit holds for almost every field and then path. -/
theorem ae_field_ae_exists_regular_uniform_limit_nonpositive_halfDiscClock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (hα : α ≤ 0) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x,
      ∃ F : Icc (0 : ℝ) 1 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        TendstoUniformly
          (fun i (t : Icc (0 : ℝ) 1) =>
            stoppedAnnularClock (fun z => (dyadicScale (i+1))^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (i+1)) z)) 0
                (fun _ => t.1.toNNReal) b) F atTop :=
  Measure.ae_ae_of_ae_prod
    (ae_prod_exists_regular_uniform_limit_nonpositive_halfDiscClock hh x hγ hγ2 hα)

end HarmonicBalls
