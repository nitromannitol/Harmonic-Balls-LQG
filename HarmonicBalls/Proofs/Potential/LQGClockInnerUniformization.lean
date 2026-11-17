import HarmonicBalls.Proofs.Potential.LQGClockInsertedCutoffLimit

/-! # Uniform control from nested cutoffs

Monotone cutoff families admit uniform control over a countable scale parameter.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- For a nested family, convergence at each scale and at each cutoff, together
with vanishing cutoff limits, gives uniform convergence over all scales. -/
theorem tendsto_iSup_zero_of_antitone_cutoff
    (X : ℕ → ℕ → ℝ≥0∞) (L : ℕ → ℝ≥0∞)
    (hmono : ∀ i, Antitone (fun n => X n i))
    (hcol : ∀ i, Tendsto (fun n => X n i) atTop (𝓝 0))
    (hrow : ∀ n, Tendsto (fun i => X n i) atTop (𝓝 (L n)))
    (hL : Tendsto L atTop (𝓝 0)) :
    Tendsto (fun n => ⨆ i, X n i) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro η hη
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hL.eventually (Iio_mem_nhds hη))
  have hLsmall : L n₀ < η := hn₀ n₀ le_rfl
  obtain ⟨m, hm⟩ := eventually_atTop.1 ((hrow n₀).eventually (Iic_mem_nhds hLsmall))
  have hfinite : ∀ᶠ n in atTop, ∀ i : Fin m, X n i ≤ η := by
    rw [eventually_all]
    intro i
    exact (hcol i).eventually (Iic_mem_nhds hη)
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 hfinite
  refine ⟨max n₀ n₁, ?_⟩
  intro n hn
  apply iSup_le
  intro i
  by_cases hi : i < m
  · exact hn₁ n (le_trans (le_max_right _ _) hn) ⟨i, hi⟩
  · exact (hmono i (le_trans (le_max_left _ _) hn)).trans
      (hm i (Nat.le_of_not_gt hi))

private theorem continuous_integrable_unit_path_occupation (b : ContinuousPath ℂ)
    (f : ℂ → ℝ) (hf : Continuous f) :
    Integrable f (Measure.map (fun t => b t)
      (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) := by
  have ht : Integrable (fun s : ℝ => f (b s.toNNReal))
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (hf.comp (b.continuous.comp continuous_real_toNNReal)).integrableOn_Icc
  have hν : Integrable (fun t : ℝ≥0 => f (b t))
      (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))) :=
    (integrable_map_measure (hf.comp b.continuous).aestronglyMeasurable
      continuous_real_toNNReal.measurable.aemeasurable).2 ht
  exact (integrable_map_measure hf.aestronglyMeasurable b.continuous.measurable.aemeasurable).2 hν

/-- The supremum over all dyadic smoothing scales of the actual unit-time
closed-cutoff occupations tends to zero under the field-path product law. -/
theorem ae_prod_tendsto_iSup_inserted_closedBall_occupation_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) :
    ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      let μ := Measure.map (fun t => q.2 t)
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
      Tendsto (fun n : ℕ => ⨆ i : ℕ,
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (i+1)
        ENNReal.ofReal (∫ z, {z : ℂ | ‖z‖ ≤ (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator
          (fun z => ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) z ∂μ))
        atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let d : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n+1)
  have hd (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have hdhalf (n : ℕ) : d n ≤ 1/2 := by
    dsimp [d]
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hdlt (n : ℕ) : d (n+1) < d n := by
    dsimp [d]
    rw [show n+1+1 = (n+1)+1 by omega, pow_succ]
    have h : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
    nlinarith
  have hdanti : Antitone d := antitone_nat_of_succ_le (fun n => (hdlt n).le)
  let p : ℝ := (2 + γ*α)/2
  have hqp : γ*α < p := by dsimp [p]; linarith
  have hp : p < 2 := by dsimp [p]; linarith
  have hconv : ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∀ n : ℕ,
        let μ := Measure.map (fun t => q.2 t)
          (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
        ∃ L : ℝ, Tendsto (fun i : ℕ =>
          ∫ z, {z : ℂ | ‖z‖ ≤ d (n+1) ∧ ‖z‖ ≤ 1/2}.indicator
            (fun z => (d i)^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (d i) z)) z ∂μ)
          atTop (𝓝 L) := by
    apply ae_all_iff.mpr
    intro n
    exact ae_prod_tendsto_inserted_closedBall_occupation hh x hq0 hq2 hγ hsub (d (n+1))
  have hfixed : ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∀ i : ℕ, Tendsto (fun n : ℕ =>
        ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < d n}.indicator (fun z => (d i)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (d i) z)) (q.2 s.toNNReal)))
        atTop (𝓝 0) := by
    apply ae_all_iff.mpr
    intro i
    have hs := ae_tsum_inner_inserted_sequence_lt_top hh x γ α p (fun _ => d i)
      (fun _ => hd i) (fun _ => hdhalf i) hq0 hqp hp
    filter_upwards [hs] with q hq
    exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hq.ne
  have hvanish := ae_prod_tendsto_inserted_closedBall_limits_zero hh x hq0 hq2 hγ hsub
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  filter_upwards [hconv, hfixed, hvanish,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hcont,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae
      (ae_recentered_inserted_circle_average hh α)] with q hconv hfixed hvanish hc hr
  let μ := Measure.map (fun t => q.2 t)
    (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
  let F : ℕ → ℂ → ℝ := fun i z => (d i)^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (d i) z)
  let E : ℕ → Set ℂ := fun n => {z | ‖z‖ ≤ d (n+1) ∧ ‖z‖ ≤ 1/2}
  let I : ℕ → Set ℂ := fun n => {z | ‖z‖ < d n}
  let A : ℕ → ℕ → ℝ := fun n i => ∫ z, (E n).indicator (F i) z ∂μ
  let B : ℕ → ℕ → ℝ≥0∞ := fun n i => ∫⁻ s in Ioc (0 : ℝ) 1,
    ENNReal.ofReal ((I n).indicator (F i) (q.2 s.toNNReal))
  have hF (i : ℕ) : Continuous (F i) := by
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (d i) z) =
        fun z => hcirc q.1 (d i) z - hcirc q.1 1 0 - α * Real.log (max (d i) ‖z‖) := by
      funext z
      exact (hr (d i) z (hd i)).symm
    have hcircins : Continuous
        (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (d i) z) := by
      rw [heq]
      exact ((hc _ (hd i)).sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left (hd i)).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hcircins))
  have hF0 (i : ℕ) (z : ℂ) : 0 ≤ F i z :=
    mul_nonneg (Real.rpow_nonneg (hd i).le _) (Real.exp_pos _).le
  have hE (n : ℕ) : MeasurableSet (E n) :=
    (measurableSet_le measurable_norm measurable_const).inter
      (measurableSet_le measurable_norm measurable_const)
  have hint (n i : ℕ) : Integrable ((E n).indicator (F i)) μ :=
    (continuous_integrable_unit_path_occupation q.2 (F i) (hF i)).indicator (hE n)
  have hAB (n i : ℕ) : ENNReal.ofReal (A n i) ≤ B n i := by
    have hsubE : E n ⊆ I n := fun z hz => lt_of_le_of_lt hz.1 (hdlt n)
    have hinner := inner_indicator_integrable_and_lintegral_eq q.2 (F i) (hF i) (hF0 i) (hdhalf n)
    have hle : A n i ≤ ∫ z, (I n).indicator (F i) z ∂μ := by
      apply integral_mono_ae (hint n i) hinner.1
      exact Eventually.of_forall (Set.indicator_le_indicator_of_subset hsubE (hF0 i))
    change ENNReal.ofReal (A n i) ≤ ∫⁻ s in Ioc (0 : ℝ) 1,
      ENNReal.ofReal ({z : ℂ | ‖z‖ < d n}.indicator (F i) (q.2 s.toNNReal))
    rw [hinner.2]
    exact ENNReal.ofReal_le_ofReal hle
  have hmono (i : ℕ) : Antitone (fun n => ENNReal.ofReal (A n i)) := by
    intro n m hnm
    apply ENNReal.ofReal_le_ofReal
    apply integral_mono_ae (hint m i) (hint n i)
    apply Eventually.of_forall
    apply Set.indicator_le_indicator_of_subset _ (hF0 i)
    intro z hz
    exact ⟨hz.1.trans (hdanti (Nat.succ_le_succ hnm)), hz.2⟩
  have hcol (i : ℕ) : Tendsto (fun n => ENNReal.ofReal (A n i)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hfixed i)
      (fun _ => zero_le) (fun n => hAB n i)
  have hrow (n : ℕ) : Tendsto (fun i => ENNReal.ofReal (A n i)) atTop
      (𝓝 (ENNReal.ofReal (limUnder atTop (A n)))) :=
    ENNReal.tendsto_ofReal (tendsto_nhds_limUnder (hconv n))
  have hL : Tendsto (fun n => ENNReal.ofReal (limUnder atTop (A n))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hvanish
  exact tendsto_iSup_zero_of_antitone_cutoff (fun n i => ENNReal.ofReal (A n i))
    (fun n => ENNReal.ofReal (limUnder atTop (A n))) hmono hcol hrow hL


/-- The supremum over dyadic smoothing scales vanishes for almost every field
and then almost every Brownian path. -/
theorem ae_field_ae_tendsto_iSup_inserted_closedBall_occupation_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x,
      let μ := Measure.map (fun t => b t)
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
      Tendsto (fun n : ℕ => ⨆ i : ℕ,
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (i+1)
        ENNReal.ofReal (∫ z, {z : ℂ | ‖z‖ ≤ (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator
          (fun z => ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) z ∂μ))
        atTop (𝓝 0) :=
  Measure.ae_ae_of_ae_prod
    (ae_prod_tendsto_iSup_inserted_closedBall_occupation_zero hh x hq0 hq2 hγ hsub)


end HarmonicBalls
