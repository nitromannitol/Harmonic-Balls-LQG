import HarmonicBalls.Proofs.Potential.LQGClockExteriorClockConvergence

/-! # Convergence of the clock without insertion for every `γ < 2`

Without insertion (`α = 0`) the closed half-disc `{‖z‖ ≤ 1/2}` plays no special role: the
density is the plain normalized circle-average density of the field. For `0 < γ < 2` the
dyadic half-disc clocks converge at countably many path-dependent horizons
(`ae_brownian_field_tendsto_countable_occupation_tests` with the indicator of the half-disc as
test function), and their dyadic time cells have `p`-th moments at most `C h ^ a` with `a > 1`
for `γ ^ 2 < 4` (`exists_halfDisc_cell_rpow_le`). The dyadic cell moment criterion gives almost
sure uniform convergence on the unit time interval, the Markov property at integer times gives
locally uniform convergence on `[0, ∞)`, and adding the exterior clocks gives the full clock.

This is the convergence of the Liouville Brownian motion clock of Berestycki
(arXiv:1301.3356, Section 2) for the whole-plane field without insertion and every `γ < 2`.

## Main results

* `exists_halfDisc_dyadic_cell_moment_zero`: dyadic half-disc cell moments under the product law.
* `ae_tendstoUniformlyOn_halfDisc_clock_zero`: uniform convergence on `[0, 1]`.
* `ae_exists_locally_uniform_limit_halfDisc_clock_zero`: locally uniform convergence on `[0, ∞)`.
* `ae_exists_locally_uniform_limit_clock_zero`: the full clock, `0 < γ < 2`.
* `forall_ae_exists_locally_uniform_limit_clock_zero_of_two_le_sq`: the same for
  `√2 ≤ γ < 2` and fields on `Type`, as a single proposition.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped NNReal ENNReal

namespace HarmonicBalls

private theorem halfDisc_occupation_eq_time (b : ContinuousPath ℂ) (T : ℝ≥0)
    (f : ℂ → ℝ) (hf : Measurable f) :
    (∫ z, f z ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
      (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic T)))) =
    ∫ s in (0 : ℝ)..(min (1 : ℝ≥0) T : ℝ), f (b s.toNNReal) := by
  rw [integral_map b.continuous.measurable.aemeasurable hf.aestronglyMeasurable]
  rw [Measure.restrict_map continuous_real_toNNReal.measurable measurableSet_Iic]
  rw [Measure.restrict_restrict (continuous_real_toNNReal.measurable measurableSet_Iic)]
  rw [integral_map (f := fun t : ℝ≥0 => f (b t)) continuous_real_toNNReal.measurable.aemeasurable
    (hf.comp b.continuous.measurable).aestronglyMeasurable]
  simp only [NNReal.coe_one]
  rw [intervalIntegral.integral_of_le
    (show (0 : ℝ) ≤ min (1 : ℝ) (T : ℝ) from le_min zero_le_one T.coe_nonneg),
    ← integral_Icc_eq_integral_Ioc]
  congr 1
  congr 1
  ext s
  simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Icc, le_min_iff]
  constructor
  · rintro ⟨hs, h0, h1⟩
    exact ⟨h0, h1, (Real.toNNReal_le_iff_le_coe).mp hs⟩
  · rintro ⟨h0, h1, hT⟩
    exact ⟨(Real.toNNReal_le_iff_le_coe).mpr hT, h0, h1⟩

/-- Without insertion, the dyadic half-disc clocks have limits at any countable family of
path-dependent unit-time horizons, for `0 < γ < 2`. -/
theorem ae_brownian_field_tendsto_countable_halfDisc_clocks_zero
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ) (T : ι → ContinuousPath ℂ → ℝ≥0) :
    ∀ᵐ b ∂planarBrownianMotion x, ∀ᵐ ω ∂P, ∀ i,
      ∃ L : ℝ, Tendsto (fun n : ℕ =>
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        ∫ s in (0 : ℝ)..(min (1 : ℝ≥0) (T i b) : ℝ),
          {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z)) (b s.toNNReal))
        atTop (𝓝 L) := by
  let A : Set ℂ := {z | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let g : ℂ → ℝ := A.indicator (fun _ => 1)
  have hgm : Measurable g := measurable_const.indicator hA
  have hgK : ∀ z, |g z| ≤ 1 := by
    intro z
    by_cases hz : z ∈ A
    · rw [show g z = 1 from Set.indicator_of_mem hz _, abs_one]
    · rw [show g z = 0 from Set.indicator_of_notMem hz _, abs_zero]
      exact zero_le_one
  have hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ 1 - 1/2 := by
    intro z hz
    have hzA : z ∈ A := by
      by_contra h
      exact hz (Set.indicator_of_notMem h _)
    linarith [hzA.2]
  have hs := ae_brownian_field_tendsto_countable_occupation_tests (ι := ι) hh hγ0 hγ2 x
    (R := 1) one_pos hgm zero_le_one hgK hgs
  filter_upwards [hs] with b hb
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let μ (i : ι) : Measure ℂ := Measure.map (fun t => b t) (ν.restrict (Iic (T i b)))
  have hμ (i : ι) : μ i ≤ Measure.map (fun t => b t) ν :=
    Measure.map_mono Measure.restrict_le_self b.continuous.measurable
  filter_upwards [hb μ hμ, hh.ae_circleAverage_one_zero,
    ae_forall_continuous_inserted_density hh γ 0] with ω hω hone hc i
  obtain ⟨L, hL⟩ := hω i
  refine ⟨L, Tendsto.congr (fun n => ?_) hL⟩
  let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
  have he : 0 < ε := by dsimp [ε]; positivity
  have heq : (fun z => g z * (ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0)))) =
      A.indicator (fun z => ε^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z)) := by
    funext z
    by_cases hz : z ∈ A
    · rw [show g z = 1 from Set.indicator_of_mem hz _, Set.indicator_of_mem hz, one_mul, hone]
      simp only [LatticeProb.Gauss.fieldCircleAverage, zero_mul, sub_zero]
    · rw [show g z = 0 from Set.indicator_of_notMem hz _, Set.indicator_of_notMem hz, zero_mul]
  change (∫ z, g z * (ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0))) ∂(μ i)) =
    ∫ s in (0 : ℝ)..(min (1 : ℝ≥0) (T i b) : ℝ),
      A.indicator (fun z => ε^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z)) (b s.toNNReal)
  rw [heq]
  exact halfDisc_occupation_eq_time b (T i b) _ ((hc ε he).measurable.indicator hA)

/-- **Dyadic half-disc cell moments without insertion.** For `γ ^ 2 < 4` there are `p > 0`,
`a > 1` and `C` such that, from every Brownian start, for all dyadic smoothing radii and all
dyadic time cells `(j / 2^m, (j + 1) / 2^m]` with `j < 2^m`, the product-law `p`-th moment of
the half-disc clock increment is at most `C (2^m)⁻¹ ^ a`. -/
theorem exists_halfDisc_dyadic_cell_moment_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ2 : γ ^ 2 < 4) :
    ∃ p a C : ℝ, 0 < p ∧ 1 < a ∧ ∀ y : ℂ, ∀ᶠ n in atTop, ∀ m j : ℕ, j < 2 ^ m →
      ∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc ((j : ℝ) / 2 ^ m) ((j + 1) / 2 ^ m),
        ENNReal.ofReal ({z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
          dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (dyadicScale (n + 1)) z))
          (q.2 s.toNNReal))) ^ p ∂(P.prod (planarBrownianMotion y)) ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ m)⁻¹ ^ a) := by
  obtain ⟨p, a, hp1, -, -, -, ha1, C, hCt, hcell⟩ := exists_halfDisc_cell_rpow_le hh hγ2
  refine ⟨p, a, C.toReal, by linarith, ha1, fun y => Eventually.of_forall fun n m j _ => ?_⟩
  set ε : ℝ := dyadicScale (n + 1)
  have hε : 0 < ε := dyadicScale_pos (n + 1)
  have hε2 : ε ≤ 1 / 2 := by
    show (2 : ℝ)⁻¹ ^ (n + 1) ≤ 1 / 2
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  set hc : ℝ := ((2 : ℝ) ^ m)⁻¹ with hhc
  have hc0 : 0 < hc := by positivity
  have hc1 : hc ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, (t : ℝ) = (j : ℝ) / 2 ^ m := ⟨⟨_, by positivity⟩, rfl⟩
  have hend : (j + 1 : ℝ) / 2 ^ m = (t : ℝ) + hc := by
    rw [ht, hhc]
    field_simp
  let A : Set ℂ := {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}
  have hpt (ω : Ω) (w : ℂ) :
      ENNReal.ofReal (A.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z)) w) =
      A.indicator (normalizedCircleDensity hcirc γ ε ω) w := by
    by_cases hz : w ∈ A
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      simp only [normalizedCircleDensity, LatticeProb.Gauss.fieldCircleAverage, zero_mul, sub_zero]
      rw [Real.rpow_def_of_pos hε, ← Real.exp_add]
      congr 2
      ring
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, ENNReal.ofReal_zero]
  calc _ ≤ ∫⁻ ω, ∫⁻ b, (∫⁻ s in Ioc ((j : ℝ) / 2 ^ m) ((j + 1) / 2 ^ m),
          ENNReal.ofReal (A.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z)) (b s.toNNReal))) ^ p
          ∂planarBrownianMotion y ∂P := lintegral_prod_le _
    _ = ∫⁻ ω, ∫⁻ b, (∫⁻ s in Ioc (t : ℝ) ((t : ℝ) + hc),
          A.indicator (normalizedCircleDensity hcirc γ ε ω) (b s.toNNReal)) ^ p
          ∂planarBrownianMotion y ∂P := by
        rw [← ht, ← hend]
        simp only [hpt]
    _ ≤ C * ENNReal.ofReal (hc ^ a) := hcell ε hε hε2 y t hc hc0 hc1
    _ = ENNReal.ofReal (C.toReal * hc ^ a) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCt.ne]

/-- **Half-disc clocks without insertion on the unit interval.** For `0 < γ < 2`, a Brownian
start `x` and a measurable nonnegative path functional `σ`, almost surely under the field-path
product law the half-disc clocks stopped at time `σ` converge uniformly on `[0, 1]` to a
continuous, nondecreasing and nonnegative limit. -/
theorem ae_tendstoUniformlyOn_halfDisc_clock_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ)
    {σ : ContinuousPath ℂ → ℝ} (hσ : Measurable σ) (hσ0 : ∀ b, 0 ≤ σ b) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), ∃ F : ℝ → ℝ,
      ContinuousOn F (Icc 0 1) ∧ MonotoneOn F (Icc 0 1) ∧ (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ F t) ∧
      TendstoUniformlyOn (fun n (t : ℝ) =>
        ∫ s in (0 : ℝ)..min t (σ q.2),
          {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
            dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (dyadicScale (n + 1)) z))
            (q.2 s.toNNReal)) F atTop (Icc 0 1) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨p, a, C, hp, ha, hmom0⟩ :=
    exists_halfDisc_dyadic_cell_moment_zero hh (show γ ^ 2 < 4 by nlinarith)
  have hmom := hmom0 x
  let μ := P.prod (planarBrownianMotion x)
  let A : Set ℂ := {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let dens (ω : Ω) (n : ℕ) (z : ℂ) : ℝ := dyadicScale (n + 1) ^ (γ ^ 2 / 2) *
    Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) (dyadicScale (n + 1)) z)
  have hdens0 (ω : Ω) (n : ℕ) (z : ℂ) : 0 ≤ dens ω n z :=
    mul_nonneg (Real.rpow_nonneg (dyadicScale_pos (n + 1)).le _) (Real.exp_pos _).le
  choose M hMm hMr hMae using fun n : ℕ =>
    exists_measurable_stopped_indicator_clock_prod_time hh (dyadicScale_pos (n + 1)) γ 0 hA hσ hσ0
  let X : ℕ → Ω × ContinuousPath ℂ → ℝ → ℝ := fun n q t => M n (q, t.toNNReal)
  have hXm (n : ℕ) (t : ℝ) : Measurable fun q => X n q t :=
    (hMm n).comp (measurable_id.prodMk measurable_const)
  have hXmono (q : Ω × ContinuousPath ℂ) (n : ℕ) : MonotoneOn (X n q) (Icc 0 1) :=
    ((hMr n q).2.1.comp fun _ _ h => Real.toNNReal_le_toNNReal h).monotoneOn _
  have hXcont (q : Ω × ContinuousPath ℂ) (n : ℕ) : ContinuousOn (X n q) (Icc 0 1) :=
    ((hMr n q).1.comp continuous_real_toNNReal).continuousOn
  have hgood : ∀ᵐ ω ∂P, (∀ (n : ℕ) (b : ContinuousPath ℂ) (t : ℝ≥0), M n ((ω, b), t) =
      ∫ s in (0 : ℝ)..min (t : ℝ) (σ b),
        A.indicator (dens ω n) (b s.toNNReal)) ∧ ∀ n, Continuous (dens ω n) := by
    filter_upwards [ae_all_iff.mpr hMae, ae_forall_continuous_inserted_density hh γ 0]
      with ω h1 h2
    exact ⟨h1, fun n => h2 _ (dyadicScale_pos (n + 1))⟩
  have hgood' : ∀ᵐ q ∂μ, (∀ (n : ℕ) (b : ContinuousPath ℂ) (t : ℝ≥0), M n ((q.1, b), t) =
      ∫ s in (0 : ℝ)..min (t : ℝ) (σ b),
        A.indicator (dens q.1 n) (b s.toNNReal)) ∧ ∀ n, Continuous (dens q.1 n) :=
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hgood
  have hconv : ∀ᵐ q ∂μ, ∀ m j : ℕ, j ≤ 2 ^ m →
      ∃ L : ℝ, Tendsto (fun n => X n q (j / 2 ^ m)) atTop (𝓝 L) := by
    have he : {q : Ω × ContinuousPath ℂ | ∀ m j : ℕ, j ≤ 2 ^ m →
        ∃ L : ℝ, Tendsto (fun n => X n q (j / 2 ^ m)) atTop (𝓝 L)} =
        ⋂ m : ℕ, ⋂ j : ℕ, {q | j ≤ 2 ^ m →
          ∃ L : ℝ, Tendsto (fun n => X n q (j / 2 ^ m)) atTop (𝓝 L)} := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    have hset : MeasurableSet {q : Ω × ContinuousPath ℂ | ∀ m j : ℕ, j ≤ 2 ^ m →
        ∃ L : ℝ, Tendsto (fun n => X n q (j / 2 ^ m)) atTop (𝓝 L)} := by
      rw [he]
      exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun j =>
        (MeasurableSet.const _).imp
          (measurableSet_exists_tendsto fun n => hXm n _)
    refine (Measure.ae_prod_iff_ae_ae hset).2 ((Measure.ae_ae_comm hset).2 ?_)
    have h40 := ae_brownian_field_tendsto_countable_halfDisc_clocks_zero (ι := ℕ × ℕ)
      hh hγ0 hγ2 x (fun i b => min (((i.2 : ℝ) / 2 ^ i.1).toNNReal) (σ b).toNNReal)
    filter_upwards [h40] with b hb
    filter_upwards [hb, hgood] with ω hω hωg
    intro m j hj
    obtain ⟨L, hL⟩ := hω (m, j)
    have hT1 : ((j : ℝ) / 2 ^ m).toNNReal ≤ 1 := by
      rw [Real.toNNReal_le_one]
      exact div_le_one_of_le₀ (by exact_mod_cast hj) (by positivity)
    have hmin : ((min (1 : ℝ≥0) (min (((j : ℝ) / 2 ^ m).toNNReal)
        (σ b).toNNReal) : ℝ≥0) : ℝ) = min ((((j : ℝ) / 2 ^ m).toNNReal : ℝ≥0) : ℝ) (σ b) := by
      rw [min_eq_right ((min_le_left _ _).trans hT1), NNReal.coe_min,
        Real.coe_toNNReal _ (hσ0 b)]
    refine ⟨L, Tendsto.congr (fun n => ?_) hL⟩
    show (∫ s in (0 : ℝ)..((min (1 : ℝ≥0) (min (((j : ℝ) / 2 ^ m).toNNReal)
        (σ b).toNNReal) : ℝ≥0) : ℝ),
          A.indicator (dens ω n) (b s.toNNReal)) =
      M n ((ω, b), ((j : ℝ) / 2 ^ m).toNNReal)
    rw [hωg.1 n b, hmin]
  have hmom' : ∀ᶠ n in atTop, ∀ m j : ℕ, j < 2 ^ m →
      ∫⁻ q, ENNReal.ofReal (X n q ((j + 1) / 2 ^ m) - X n q (j / 2 ^ m)) ^ p ∂μ ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ m)⁻¹ ^ a) := by
    filter_upwards [hmom] with n hn
    intro m j hj
    refine le_trans (lintegral_mono_ae ?_) (hn m j hj)
    filter_upwards [hgood'] with q hq
    have hu : (0 : ℝ) ≤ j / 2 ^ m := by positivity
    have huv : (j : ℝ) / 2 ^ m ≤ (j + 1) / 2 ^ m :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h1 : X n q ((j + 1) / 2 ^ m) =
        ∫ s in (0 : ℝ)..min ((j + 1) / 2 ^ m) (σ q.2),
          A.indicator (dens q.1 n) (q.2 s.toNNReal) := by
      have h := hq.1 n q.2 (((j : ℝ) + 1) / 2 ^ m).toNNReal
      rwa [Real.coe_toNNReal _ (hu.trans huv)] at h
    have h0 : X n q (j / 2 ^ m) =
        ∫ s in (0 : ℝ)..min (j / 2 ^ m) (σ q.2),
          A.indicator (dens q.1 n) (q.2 s.toNNReal) := by
      have h := hq.1 n q.2 ((j : ℝ) / 2 ^ m).toNNReal
      rwa [Real.coe_toNNReal _ hu] at h
    rw [h1, h0]
    refine ENNReal.rpow_le_rpow ?_ hp.le
    exact ofReal_stopped_integral_sub_le_lintegral
      (fun s => Set.indicator_nonneg (fun z _ => hdens0 q.1 n z) _)
      (fun u v => intervalIntegrable_indicator_along_path _ (hq.2 n) hA q.2 u v) huv
  have hmain := ae_exists_continuousOn_monotoneOn_limit_of_dyadic_cell_moment (μ := μ) X
    (Eventually.of_forall hXmono) (Eventually.of_forall hXcont) hXm hconv hp ha hmom'
  filter_upwards [hmain, hgood'] with q hF hq
  obtain ⟨F, hFc, hFm, hFu⟩ := hF
  have hEq (n : ℕ) : EqOn (X n q) (fun t =>
      ∫ s in (0 : ℝ)..min t (σ q.2), A.indicator (dens q.1 n) (q.2 s.toNNReal)) (Icc 0 1) := by
    intro t ht
    have h1 := hq.1 n q.2 t.toNNReal
    rw [Real.coe_toNNReal t ht.1] at h1
    exact h1
  refine ⟨F, hFc, hFm, fun t ht => ?_, hFu.congr (Eventually.of_forall hEq)⟩
  exact ge_of_tendsto' (hFu.tendsto_at ht) fun n => (hMr n q).2.2 t.toNNReal

/-- For `0 < γ < 2`, the unit-interval convergence of the half-disc clocks without insertion
holds simultaneously after every integer time shift. -/
theorem ae_exists_uniform_limit_integer_shift_halfDisc_clock_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), ∀ k : ℕ, ∃ F : Icc (0 : ℝ) 1 → ℝ,
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ u : Icc (0 : ℝ) 1,
        |(∫ s in (0 : ℝ)..(u : ℝ), {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
            dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (dyadicScale (n + 1)) z))
          ((ContinuousPath.shift (k : ℝ≥0) q.2) s.toNNReal)) - F u| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let A : Set ℂ := {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  choose M hMm hMr hMae using fun n : ℕ =>
    exists_measurable_stopped_indicator_clock_prod_time hh (dyadicScale_pos (n + 1)) γ 0 hA
      (measurable_const (a := (1 : ℝ))) (fun _ => zero_le_one)
  let B (n : ℕ) (q : Ω × ContinuousPath ℂ) : C(Icc (0 : ℝ) 1, ℝ) :=
    ⟨fun t => M n (q, (t : ℝ).toNNReal),
      (hMr n q).1.comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩
  have hBm (n : ℕ) : Measurable (B n) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (hMm n).comp (measurable_id.prodMk measurable_const)
  let S : Set (Ω × ContinuousPath ℂ) := {q | ∃ F, Tendsto (fun n => B n q) atTop (𝓝 F)}
  have hSm : MeasurableSet S := measurableSet_exists_tendsto hBm
  have hS (y : ℂ) : ∀ᵐ q ∂(P.prod (planarBrownianMotion y)), q ∈ S := by
    filter_upwards [ae_tendstoUniformlyOn_halfDisc_clock_zero hh hγ0 hγ2 y
      (measurable_const (a := (1 : ℝ))) (fun _ => zero_le_one),
      (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion y)).ae
        (ae_all_iff.mpr hMae)] with q hq hM
    obtain ⟨F, hFc, -, -, hF⟩ := hq
    let G : C(Icc (0 : ℝ) 1, ℝ) :=
      ⟨fun t => F t, hFc.comp_continuous continuous_subtype_val (fun t => t.2)⟩
    refine ⟨G, ?_⟩
    apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
    rw [Metric.tendstoUniformlyOn_iff] at hF
    rw [Metric.tendstoUniformly_iff]
    intro η hη
    filter_upwards [hF η hη] with n hn t
    have h := hn t t.2
    have hMt := hM n q.2 (t : ℝ).toNNReal
    rw [Real.coe_toNNReal _ t.2.1] at hMt
    change dist (F t) (M n (q, (t : ℝ).toNNReal)) < η
    rw [show M n (q, (t : ℝ).toNNReal) = _ from hMt]
    simpa only [A, min_eq_left t.2.2] using h
  apply ae_all_iff.mpr
  intro k
  have hshift := ae_prod_planarBrownianMotion_shift_of_forall_ae P x k S hSm hS
  filter_upwards [hshift, (Measure.quasiMeasurePreserving_fst
    (μ := P) (ν := planarBrownianMotion x)).ae (ae_all_iff.mpr hMae)] with q hq hM
  obtain ⟨F, hF⟩ := hq
  refine ⟨F, ?_⟩
  have hu := ContinuousMap.tendsto_iff_tendstoUniformly.mp hF
  rw [Metric.tendstoUniformly_iff] at hu
  intro η hη
  filter_upwards [hu η hη] with n hn u
  have heq := hM n (ContinuousPath.shift (k : ℝ≥0) q.2) (u : ℝ).toNNReal
  rw [Real.coe_toNNReal _ u.2.1] at heq
  have h := hn u
  change dist (F u) (M n ((q.1, ContinuousPath.shift (k : ℝ≥0) q.2), (u : ℝ).toNNReal)) < η at h
  rw [heq, dist_comm, Real.dist_eq] at h
  simpa only [A, min_eq_left u.2.2] using h

/-- **Half-disc clocks without insertion on finite horizons.** For `0 < γ < 2`, the dyadic
half-disc clocks converge locally uniformly on `[0, ∞)` to a continuous, nonnegative and
nondecreasing limit, almost surely under the field-path product law. -/
theorem ae_exists_locally_uniform_limit_halfDisc_clock_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ) :
    ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ),
            {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (dyadicScale (j+1)) z))
                  (q.2 s.toNNReal)) - F t| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hA : MeasurableSet {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2} :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  filter_upwards [ae_exists_uniform_limit_integer_shift_halfDisc_clock_zero hh hγ0 hγ2 x,
    (Measure.quasiMeasurePreserving_fst (μ := P)
      (ν := planarBrownianMotion x)).ae (ae_forall_continuous_inserted_density hh γ 0)]
    with q hq hc
  let f (n : ℕ) : ℂ → ℝ := fun z => dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (dyadicScale (n + 1)) z)
  have hfc (n : ℕ) : Continuous (f n) := hc _ (dyadicScale_pos (n + 1))
  let g (n : ℕ) (t : ℝ) : ℝ :=
    {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (f n) (q.2 t.toNNReal)
  let Acl (n : ℕ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, g n s
  have hblock : ∀ k : ℕ, ∃ F : Icc (0 : ℝ) 1 → ℝ,
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ u : Icc (0 : ℝ) 1,
        |(Acl n ((k : ℝ) + u) - Acl n k) - F u| < η := by
    intro k
    obtain ⟨F, hF⟩ := hq k
    refine ⟨F, fun η hη => ?_⟩
    filter_upwards [hF η hη] with n hn u
    have heq := integral_indicator_shift_eq_sub (f n) (hfc n) hA q.2 k u.2.1
    change (∫ s in (0 : ℝ)..(u : ℝ), _) = Acl n (k + u) - Acl n k at heq
    rw [← heq]
    exact hn u
  have hnat := exists_uniform_limit_on_nat_intervals_of_unit_blocks Acl
    (fun n => intervalIntegral.integral_same) hblock
  let B (n : ℕ) (t : ℝ≥0) := Acl n t
  have hBc (n : ℕ) : Continuous (B n) :=
    (intervalIntegral.continuous_primitive (fun u v =>
      intervalIntegrable_indicator_along_path (f n) (hfc n) hA q.2 u v) 0).comp
        continuous_subtype_val
  have hf0 (n : ℕ) (z : ℂ) : 0 ≤ f n z :=
    mul_nonneg (Real.rpow_nonneg (dyadicScale_pos (n + 1)).le _) (Real.exp_pos _).le
  have hg0 (n : ℕ) (t : ℝ) : 0 ≤ g n t := Set.indicator_nonneg (fun z _ => hf0 n z) _
  have hB0 (n : ℕ) (t : ℝ≥0) : 0 ≤ B n t :=
    intervalIntegral.integral_nonneg_of_forall t.coe_nonneg (hg0 n)
  have hBm (n : ℕ) : Monotone (B n) := by
    intro s t hst
    exact intervalIntegral.integral_mono_interval le_rfl s.coe_nonneg hst
      (Eventually.of_forall (hg0 n))
      (intervalIntegrable_indicator_along_path (f n) (hfc n) hA q.2 0 t)
  have hnatB (N : ℕ) : ∃ G : ℝ≥0 → ℝ, ∀ η : ℝ, 0 < η →
      ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ N → |B n t - G t| < η := by
    obtain ⟨G, hG⟩ := hnat N
    refine ⟨fun t => G t, fun η hη => ?_⟩
    filter_upwards [hG η hη] with n hn t ht
    exact hn t ⟨t.coe_nonneg, by exact_mod_cast ht⟩
  exact exists_continuous_monotone_limit_of_uniform_on_nat_intervals B hBc hB0 hBm hnatB

/-- **The clock without insertion for every `γ < 2`.** For `0 < γ < 2` and any Brownian start,
the dyadic clocks `∫₀ᵗ ε^{γ²/2} e^{γ h_ε(B_s)} ds`, `ε = 2^{-(n+1)}`, of the whole-plane field
converge locally uniformly on `[0, ∞)` to a continuous, nonnegative and nondecreasing limit,
almost surely under the field-path product law. -/
theorem ae_exists_locally_uniform_limit_clock_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ), dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (dyadicScale (n + 1))
              (q.2 s.toNNReal))) - F t| < η :=
  ae_exists_locally_uniform_limit_clock_of_halfDisc_of_cell_moment hh hγ0 hγ2 0 x
    (ae_exists_locally_uniform_limit_halfDisc_clock_zero hh hγ0 hγ2 x)
    fun R _ => exists_exterior_dyadic_cell_moment hh (show γ ^ 2 < 4 by nlinarith) 0 R

/-- **The clock without insertion for `√2 ≤ γ < 2`**, as one proposition over fields on `Type`:
for every `γ` with `0 < γ`, `2 ≤ γ ^ 2` and `γ < 2`, every whole-plane field and every start,
the dyadic clocks converge locally uniformly on `[0, ∞)` to a continuous, nonnegative and
nondecreasing limit, almost surely under the field-path product law. -/
theorem forall_ae_exists_locally_uniform_limit_clock_zero_of_two_le_sq :
    ∀ γ : ℝ, 0 < γ → 2 ≤ γ ^ 2 → γ < 2 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
        {hcirc : Ω → ℝ → ℂ → ℝ}, LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc → ∀ x : ℂ,
        ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
          ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
            ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
              |(∫ s in (0 : ℝ)..(t : ℝ), dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (dyadicScale (n + 1))
                  (q.2 s.toNNReal))) - F t| < η := by
  intro γ hγ0 _ hγ2 Ω _ P hC hcirc hh x
  exact ae_exists_locally_uniform_limit_clock_zero hh hγ0 hγ2 x

end HarmonicBalls
