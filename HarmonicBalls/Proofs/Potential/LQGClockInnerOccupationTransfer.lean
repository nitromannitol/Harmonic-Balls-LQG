import HarmonicBalls.Proofs.Potential.LQGClockInnerAnnularSplit
import HarmonicBalls.Proofs.Potential.LQGClockInnerSequences

/-! # Inner occupations along continuous paths

Nonnegative inner occupations agree with spatial integrals against the
unit-time path occupation measure.
-/

open MeasureTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- A continuous nonnegative density on an inner ball has an integrable
spatial cutoff and agrees with its nonnegative time occupation. -/
theorem inner_indicator_integrable_and_lintegral_eq
    (b : ContinuousPath ℂ) (f : ℂ → ℝ) (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z)
    {δ : ℝ} (hδ : δ ≤ 1/2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    let μ := Measure.map (fun t => b t) ν
    Integrable ({z : ℂ | ‖z‖ < δ}.indicator f) μ ∧
      (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < δ}.indicator f (b s.toNNReal))) =
      ENNReal.ofReal (∫ z, {z : ℂ | ‖z‖ < δ}.indicator f z ∂μ) := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let μ : Measure ℂ := Measure.map (fun t => b t) ν
  let I : Set ℂ := {z | ‖z‖ < δ}
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  have hI : MeasurableSet I := measurableSet_lt measurable_norm measurable_const
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (1/2 : ℝ)).bddAbove_image hf.norm.continuousOn
  have hi : Integrable (I.indicator f) μ := by
    apply (integrable_const (max K 0)).mono' (hf.measurable.indicator hI).aestronglyMeasurable
    filter_upwards with z
    by_cases hz : z ∈ I
    · have hzball : z ∈ Metric.closedBall (0 : ℂ) (1/2 : ℝ) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using (le_trans (le_of_lt hz) hδ)
      rw [show I.indicator f z = f z from Set.indicator_of_mem hz _]
      exact (hK ⟨z, hzball, rfl⟩).trans (le_max_left K 0)
    · rw [show I.indicator f z = 0 from Set.indicator_of_notMem hz _, norm_zero]
      exact le_max_right K 0
  refine ⟨hi, ?_⟩
  have hmeas : Measurable (fun z => ENNReal.ofReal (I.indicator f z)) :=
    (hf.measurable.indicator hI).ennreal_ofReal
  have heq : (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (I.indicator f (b s.toNNReal))) =
      ∫⁻ z, ENNReal.ofReal (I.indicator f z) ∂μ := by
    rw [show μ = Measure.map (fun t => b t) ν from rfl,
      lintegral_map hmeas b.continuous.measurable]
    dsimp [ν]
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
    symm
    exact lintegral_map (hmeas.comp b.continuous.measurable) continuous_real_toNNReal.measurable
  rw [heq, ← ofReal_integral_eq_lintegral_ofReal hi]
  filter_upwards with z
  change (0 : ℝ) ≤ I.indicator f z
  by_cases hz : z ∈ I
  · simpa only [Set.indicator_of_mem hz] using hf0 z
  · simp [hz]

/-- Finite sums of nonnegative time occupations yield summable real
spatial occupations for a continuous sequence of densities. -/
theorem summable_inner_integral_of_lintegral_sum_lt_top
    (b : ContinuousPath ℂ) (f : ℕ → ℂ → ℝ)
    (hf : ∀ n, Continuous (f n)) (hf0 : ∀ n z, 0 ≤ f n z)
    (δ : ℕ → ℝ) (hδ : ∀ n, δ n ≤ 1/2)
    (hs : (∑' n : ℕ, ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
      ({z : ℂ | ‖z‖ < δ n}.indicator (f n) (b s.toNNReal))) < ∞) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    let μ := Measure.map (fun t => b t) ν
    Summable (fun n => ∫ z, {z : ℂ | ‖z‖ < δ n}.indicator (f n) z ∂μ) := by
  have hsum := ENNReal.summable_toReal hs.ne
  apply hsum.congr
  intro n
  have h := (inner_indicator_integrable_and_lintegral_eq b (f n) (hf n) (hf0 n) (hδ n)).2
  rw [h, ENNReal.toReal_ofReal]
  apply integral_nonneg
  intro z
  change (0 : ℝ) ≤ {z : ℂ | ‖z‖ < δ n}.indicator (f n) z
  by_cases hz : ‖z‖ < δ n
  · rw [Set.indicator_of_mem (show z ∈ {z : ℂ | ‖z‖ < δ n} from hz)]
    exact hf0 n z
  · simp [hz]


/-- Along a deterministic smoothing sequence, the real inner occupations
are summable for almost every path and then almost every field. -/
theorem planarBrownianMotion_ae_field_ae_summable_inner_inserted_sequence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α p : ℝ) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hεhalf : ∀ n, ε n ≤ 1/2)
    (hq : 0 < γ*α) (hqp : γ*α < p) (hp : p < 2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂planarBrownianMotion x, ∀ᵐ ω ∂P,
      let μ := Measure.map (fun t => b t) ν
      Summable (fun n : ℕ => ∫ z, {z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+1)}.indicator
        (fun z => (ε n)^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε n) z)) z ∂μ) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hs := ae_tsum_inner_inserted_sequence_lt_top hh x γ α p ε hε hεhalf hq hqp hp
  have hswap := (Measure.measurePreserving_swap (μ := planarBrownianMotion x) (ν := P)).quasiMeasurePreserving.ae hs
  have hpaths := Measure.ae_ae_of_ae_prod hswap
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  filter_upwards [hpaths] with b hb
  filter_upwards [hb, hcont, ae_recentered_inserted_circle_average hh α] with ω hsum hc hr
  let F : ℕ → ℂ → ℝ := fun n z => (ε n)^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε n) z)
  have hF (n : ℕ) : Continuous (F n) := by
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε n) z) =
        fun z => hcirc ω (ε n) z - hcirc ω 1 0 - α * Real.log (max (ε n) ‖z‖) := by
      funext z
      exact (hr (ε n) z (hε n)).symm
    have hfc : Continuous (fun z => hcirc ω (ε n) z - hcirc ω 1 0 -
        α * Real.log (max (ε n) ‖z‖)) :=
      ((hc _ (hε n)).sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left (hε n)).ne')))
    have hcircins : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε n) z) := by
      rw [heq]
      exact hfc
    dsimp [F]
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      hcircins))
  have hF0 (n : ℕ) (z : ℂ) : 0 ≤ F n z := by
    dsimp [F]
    exact mul_nonneg (Real.rpow_nonneg (hε n).le _) (Real.exp_pos _).le
  have hδ (n : ℕ) : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1/2 := by
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  exact summable_inner_integral_of_lintegral_sum_lt_top b F hF hF0 _ hδ hsum


end HarmonicBalls
