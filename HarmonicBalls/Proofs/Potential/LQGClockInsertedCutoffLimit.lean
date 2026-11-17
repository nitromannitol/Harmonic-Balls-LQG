import HarmonicBalls.Proofs.Potential.LQGClockInnerLiminfDyadic
import HarmonicBalls.Proofs.Potential.LQGClockInsertedProductConvergence

/-! # Comparing cutoff limits

Vanishing lower-limit bounds control limits taken before the cutoff shrinks.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- If nonnegative approximants converge at each cutoff and are bounded by
nonnegative extended-real approximants, vanishing lower limits of the latter
force the cutoff limits to vanish. -/
theorem tendsto_limUnder_zero_of_le_liminf
    (A : ℕ → ℕ → ℝ) (B : ℕ → ℕ → ℝ≥0∞)
    (hA : ∀ n i, 0 ≤ A n i)
    (hlim : ∀ n, ∃ L : ℝ, Tendsto (A n) atTop (𝓝 L))
    (hAB : ∀ n i, ENNReal.ofReal (A n i) ≤ B n i)
    (hB : Tendsto (fun n => liminf (B n) atTop) atTop (𝓝 0)) :
    Tendsto (fun n => limUnder atTop (A n)) atTop (𝓝 0) := by
  have hlim' (n : ℕ) : Tendsto (A n) atTop (𝓝 (limUnder atTop (A n))) :=
    tendsto_nhds_limUnder (hlim n)
  have hnonneg (n : ℕ) : 0 ≤ limUnder atTop (A n) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds (hlim' n) (Eventually.of_forall (hA n))
  have hle (n : ℕ) : ENNReal.ofReal (limUnder atTop (A n)) ≤ liminf (B n) atTop := by
    rw [← (ENNReal.tendsto_ofReal (hlim' n)).liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall (hAB n))
  have hzero : Tendsto (fun n => ENNReal.ofReal (limUnder atTop (A n))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB
      (fun _ => zero_le) hle
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hzero
  have heq : (ENNReal.toReal ∘ fun n => ENNReal.ofReal (limUnder atTop (A n))) =
      (fun n => limUnder atTop (A n)) := by
    funext n
    exact ENNReal.toReal_ofReal (hnonneg n)
  rw [heq] at hreal
  simpa only [ENNReal.toReal_zero] using hreal

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

/-- After taking the dyadic smoothing limit at each closed cutoff, the actual
unit-time inserted occupations tend to zero as the cutoff shrinks. -/
theorem ae_prod_tendsto_inserted_closedBall_limits_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) :
    ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      let μ := Measure.map (fun t => q.2 t)
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
      Tendsto (fun n : ℕ => limUnder atTop (fun i : ℕ =>
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (i+1)
        ∫ z, {z : ℂ | ‖z‖ ≤ (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator
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
  have hsmall := ae_tendsto_liminf_inner_inserted_dyadic_zero
    hh x γ α p d hd hdhalf hq0 hqp hp
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  filter_upwards [hconv, hsmall,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hcont,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae
      (ae_recentered_inserted_circle_average hh α)] with q hconv hsmall hc hr
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
  have hA (n i : ℕ) : 0 ≤ A n i := by
    apply integral_nonneg
    intro z
    change (0 : ℝ) ≤ (E n).indicator (F i) z
    by_cases hz : z ∈ E n
    · rw [Set.indicator_of_mem hz]
      exact hF0 i z
    · simp [hz]
  have hAB (n i : ℕ) : ENNReal.ofReal (A n i) ≤ B n i := by
    have hsubE : E n ⊆ I n := fun z hz => lt_of_le_of_lt hz.1 (hdlt n)
    have hfi := continuous_integrable_unit_path_occupation q.2 (F i) (hF i)
    have hinner := inner_indicator_integrable_and_lintegral_eq q.2 (F i) (hF i) (hF0 i) (hdhalf n)
    have hle : A n i ≤ ∫ z, (I n).indicator (F i) z ∂μ := by
      apply integral_mono_ae (hfi.indicator (hE n)) hinner.1
      exact Eventually.of_forall (Set.indicator_le_indicator_of_subset hsubE (hF0 i))
    change ENNReal.ofReal (A n i) ≤ ∫⁻ s in Ioc (0 : ℝ) 1,
      ENNReal.ofReal ({z : ℂ | ‖z‖ < d n}.indicator (F i) (q.2 s.toNNReal))
    rw [hinner.2]
    exact ENNReal.ofReal_le_ofReal hle
  apply tendsto_limUnder_zero_of_le_liminf A B hA hconv hAB
  exact hsmall


/-- The closed-cutoff smoothing limits tend to zero for almost every field
and then almost every Brownian path. -/
theorem ae_field_ae_tendsto_inserted_closedBall_limits_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x,
      let μ := Measure.map (fun t => b t)
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
      Tendsto (fun n : ℕ => limUnder atTop (fun i : ℕ =>
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (i+1)
        ∫ z, {z : ℂ | ‖z‖ ≤ (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator
          (fun z => ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) z ∂μ))
        atTop (𝓝 0) :=
  Measure.ae_ae_of_ae_prod
    (ae_prod_tendsto_inserted_closedBall_limits_zero hh x hq0 hq2 hγ hsub)


end HarmonicBalls
