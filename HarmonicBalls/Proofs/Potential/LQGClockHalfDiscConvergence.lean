import HarmonicBalls.Proofs.Potential.LQGClockCutoffGluing

/-! # Uniform convergence of half-disc clocks

Annular convergence and vanishing inner occupations yield convergence on the
half unit disc for a restricted range of insertion and coupling parameters.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- The actual dyadic half-disc clocks converge uniformly on the unit time
interval for each fixed Brownian start, in the stated parameter range. -/
theorem ae_prod_exists_uniform_limit_halfDiscClock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ) (hγ2 : γ^2 < 2)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) :
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
    ae_prod_tendsto_iSup_time_inner_inserted_zero hh x hq0 hq2 hγ hsub,
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
theorem ae_field_ae_exists_uniform_limit_halfDiscClock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ) (hγ2 : γ^2 < 2)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x,
      ∃ F : Icc (0 : ℝ) 1 → ℝ, TendstoUniformly
        (fun i (t : Icc (0 : ℝ) 1) =>
          stoppedAnnularClock (fun z => (dyadicScale (i+1))^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (i+1)) z)) 0
              (fun _ => t.1.toNNReal) b) F atTop :=
  Measure.ae_ae_of_ae_prod
    (ae_prod_exists_uniform_limit_halfDiscClock hh x hq0 hq2 hγ hγ2 hsub)


/-- The half-disc limit has continuous, nonnegative and nondecreasing paths. -/
theorem ae_prod_exists_regular_uniform_limit_halfDiscClock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ) (hγ2 : γ^2 < 2)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) :
    ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∃ F : Icc (0 : ℝ) 1 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        TendstoUniformly
          (fun i (t : Icc (0 : ℝ) 1) =>
            stoppedAnnularClock (fun z => (dyadicScale (i+1))^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (i+1)) z)) 0
                (fun _ => t.1.toNNReal) q.2) F atTop := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let hf := Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)
  filter_upwards [ae_prod_exists_uniform_limit_halfDiscClock hh x hq0 hq2 hγ hγ2 hsub,
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

end HarmonicBalls
