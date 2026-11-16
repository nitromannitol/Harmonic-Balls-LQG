import HarmonicBalls.Proofs.Potential.BrownianUniformBallOccupation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Endpoint Brownian occupation kernels

Planar Brownian increments and ordered simultaneous visits satisfy endpoint
small-ball bounds with a truncated inverse-time kernel.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Metric
open scoped Interval NNReal ENNReal

namespace HarmonicBalls

/-- The planar increment small-ball bound with its endpoint inverse-time kernel. -/
theorem planarBrownianMotion_increment_smallBall_le_inv_time (x z : ℂ)
    {s t : ℝ≥0} (hts : t ≠ s) {r : ℝ} (hr : 0 ≤ r) :
    planarBrownianMotion x {b | ‖b t - b s - z‖ < r} ≤
      min 1 (ENNReal.ofReal ((2 / Real.pi) * r ^ 2 / |(t : ℝ) - (s : ℝ)|)) := by
  let u : ℝ := |(t : ℝ) - (s : ℝ)|
  have hu : 0 < u := by
    dsimp [u]
    apply abs_pos.mpr
    exact sub_ne_zero.mpr (by exact_mod_cast hts)
  let a : ℝ := 2 * r / Real.sqrt (2 * Real.pi * u)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hs : (Real.sqrt (2 * Real.pi * u)) ^ 2 = 2 * Real.pi * u :=
    Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (2 * Real.pi * u) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hu0 : u ≠ 0 := ne_of_gt hu
  have haeq : a ^ 2 = (2 / Real.pi) * r ^ 2 / u := by
    dsimp [a]
    field_simp
    nlinarith [hs]
  have h := planarBrownianMotion_increment_smallBall_le_uniform_center x z hts hr
  have hsmall' : planarBrownianMotion x {b | ‖b t - b s - z‖ < r} ≤
      min 1 (ENNReal.ofReal (a ^ 2)) := by
    simpa only [a, u, coe_nndist, Real.dist_eq, ENNReal.ofReal_pow ha] using h
  simpa only [haeq, u] using hsmall'

/-- Ordered simultaneous visits are bounded by a product of truncated endpoint kernels. -/
theorem planarBrownianMotion_joint_ball_le_inv_time (x z : ℂ) {n : ℕ}
    (t : Fin (n + 1) → ℝ≥0) (ht : StrictMono t) {r : ℝ} (hr : 0 ≤ r) :
    planarBrownianMotion x {b | ∀ i, ‖b (t i) - z‖ < r} ≤
      ∏ i : Fin n, min 1 (ENNReal.ofReal ((2 / Real.pi) * (2 * r) ^ 2 /
        |(t i.succ : ℝ) - (t i.castSucc : ℝ)|)) := by
  let f : Fin n → ContinuousPath ℂ → ℂ :=
    fun i b => b (t i.succ) - b (t i.castSucc)
  let A : Set ℂ := ball 0 (2 * r)
  have hi : iIndepFun f (planarBrownianMotion x) :=
    planarBrownianMotion_hasIndepIncrements x n t ht.monotone
  have hsub : {b : ContinuousPath ℂ | ∀ i, ‖b (t i) - z‖ < r} ⊆
      ⋂ i : Fin n, f i ⁻¹' A := by
    intro b hb
    simp only [mem_iInter, mem_preimage]
    intro i
    simp only [f, A, Metric.mem_ball, dist_zero_right]
    have hnorm := norm_sub_le (b (t i.succ) - z) (b (t i.castSucc) - z)
    have heq : (b (t i.succ) - z) - (b (t i.castSucc) - z) =
        b (t i.succ) - b (t i.castSucc) := by abel
    rw [heq] at hnorm
    linarith [hb i.succ, hb i.castSucc]
  calc
    _ ≤ planarBrownianMotion x (⋂ i : Fin n, f i ⁻¹' A) := measure_mono hsub
    _ = ∏ i : Fin n, planarBrownianMotion x (f i ⁻¹' A) := by
      simpa using hi.measure_inter_preimage_eq_mul Finset.univ
        (sets := fun _ => A) (fun _ _ => isOpen_ball.measurableSet)
    _ ≤ _ := by
      apply Finset.prod_le_prod
      intro i _
      have hne : t i.succ ≠ t i.castSucc :=
        ne_of_gt (ht (Fin.castSucc_lt_succ (i := i)))
      have hbound := planarBrownianMotion_increment_smallBall_le_inv_time x 0 hne
        (show 0 ≤ 2 * r by positivity)
      convert hbound using 1
      congr 1
      ext b
      simp [f, A, Metric.mem_ball, dist_zero_right]

/-- The ordered endpoint bound extends to distinct, unordered time tuples. -/
theorem planarBrownianMotion_joint_ball_le_sum_inv_time (x z : ℂ) {n : ℕ}
    (t : Fin (n + 1) → ℝ≥0) (ht : Function.Injective t) {r : ℝ} (hr : 0 ≤ r) :
    planarBrownianMotion x {b | ∀ i, ‖b (t i) - z‖ < r} ≤
      ∑ σ : Equiv.Perm (Fin (n + 1)), ∏ i : Fin n,
        min 1 (ENNReal.ofReal ((2 / Real.pi) * (2 * r) ^ 2 /
          |(t (σ i.succ) : ℝ) - (t (σ i.castSucc) : ℝ)|)) := by
  classical
  let σ := Tuple.sort t
  have hmono : StrictMono (t ∘ σ) :=
    (Tuple.monotone_sort t).strictMono_of_injective (ht.comp σ.injective)
  have h := planarBrownianMotion_joint_ball_le_inv_time x z (t ∘ σ) hmono hr
  have hsets : {b : ContinuousPath ℂ | ∀ i, ‖b (t (σ i)) - z‖ < r} =
      {b : ContinuousPath ℂ | ∀ i, ‖b (t i) - z‖ < r} := by
    ext b
    simp only [mem_ofPred_eq]
    exact (σ.surjective.forall (p := fun i => ‖b (t i) - z‖ < r)).symm
  change planarBrownianMotion x {b | ∀ i, ‖b (t (σ i)) - z‖ < r} ≤ _ at h
  rw [hsets] at h
  have hs : (∏ i : Fin n, min 1 (ENNReal.ofReal ((2 / Real.pi) * (2 * r) ^ 2 /
      |(t (σ i.succ) : ℝ) - (t (σ i.castSucc) : ℝ)|))) ≤
      ∑ τ : Equiv.Perm (Fin (n + 1)), ∏ i : Fin n,
        min 1 (ENNReal.ofReal ((2 / Real.pi) * (2 * r) ^ 2 /
          |(t (τ i.succ) : ℝ) - (t (τ i.castSucc) : ℝ)|)) := by
    apply Finset.single_le_sum (f := fun τ : Equiv.Perm (Fin (n + 1)) =>
      ∏ i : Fin n, min 1 (ENNReal.ofReal ((2 / Real.pi) * (2 * r) ^ 2 /
        |(t (τ i.succ) : ℝ) - (t (τ i.castSucc) : ℝ)|)))
    · intro τ hτ
      exact bot_le
    · exact Finset.mem_univ σ
  exact h.trans (by simpa only [Function.comp_apply] using hs)

/-- Occupation moments are controlled by endpoint kernel integrals. -/
theorem planarBrownianMotion_occupation_moment_le_inv_time (x z : ℂ) {n : ℕ}
    {r : ℝ} (hr : 0 ≤ r) (ν : Measure ℝ≥0)
    [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    (∫⁻ b : ContinuousPath ℂ, (ν {t | ‖b t - z‖ < r}) ^ (n + 1)
      ∂(planarBrownianMotion x)) ≤
    ∫⁻ t : Fin (n + 1) → ℝ≥0,
      ∑ σ : Equiv.Perm (Fin (n + 1)), ∏ i : Fin n,
        min 1 (ENNReal.ofReal ((2 / Real.pi) * (2 * r) ^ 2 /
          |(t (σ i.succ) : ℝ) - (t (σ i.castSucc) : ℝ)|))
      ∂(Measure.pi (fun _ : Fin (n + 1) => ν)) := by
  rw [planarBrownianMotion_occupation_moment_eq]
  apply lintegral_mono_ae
  filter_upwards [ae_injective_pi_of_atomless (n + 1) ν] with t ht
  exact planarBrownianMotion_joint_ball_le_sum_inv_time x z t ht hr

/-- Exact integral of the one-sided truncated inverse-time kernel. -/
theorem truncatedInvTime_integral {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ t : ℝ in 0..1, min 1 (a / t)) = a * (1 + Real.log (1 / a)) := by
  have heq0 : EqOn (fun t : ℝ => min 1 (a / t)) (fun _ => 1) (uIoo 0 a) := by
    intro t ht
    have ht' : t ∈ Ioo 0 a := by simpa [uIoo_of_le ha.le] using ht
    exact min_eq_left (one_le_div ht'.1 |>.2 ht'.2.le)
  have heq1 : EqOn (fun t : ℝ => min 1 (a / t)) (fun t => a * t⁻¹) (uIoo a 1) := by
    intro t ht
    have ht' : t ∈ Ioo a 1 := by simpa [uIoo_of_le ha1] using ht
    change min 1 (a / t) = a * t⁻¹
    rw [min_eq_right (div_le_one₀ (lt_trans ha ht'.1) |>.2 ht'.1.le), div_eq_mul_inv]
  have hi0 : IntervalIntegrable (fun t : ℝ => min 1 (a / t)) volume 0 a :=
    (intervalIntegrable_congr_uIoo heq0).2 intervalIntegrable_const
  have hi1 : IntervalIntegrable (fun t : ℝ => min 1 (a / t)) volume a 1 := by
    apply (intervalIntegrable_congr_uIoo heq1).2
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.const_mul
    apply continuousOn_inv₀.mono
    intro t ht
    have ht' : t ∈ Icc a 1 := by simpa [uIcc_of_le ha1] using ht
    simp only [mem_compl_iff, mem_singleton_iff]
    linarith [ht'.1]
  have h0 : (∫ t : ℝ in 0..a, min 1 (a / t)) = a := by
    rw [intervalIntegral.integral_congr_uIoo heq0]
    simp
  have h1 : (∫ t : ℝ in a..1, min 1 (a / t)) = a * Real.log (1 / a) := by
    rw [intervalIntegral.integral_congr_uIoo heq1]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha (by norm_num)]
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi1, h0, h1]
  ring

/-- The one-sided truncated inverse-time kernel is integrable on the unit interval. -/
theorem truncatedInvTime_intervalIntegrable {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    IntervalIntegrable (fun t : ℝ => min 1 (a / t)) volume 0 1 := by
  have heq0 : EqOn (fun t : ℝ => min 1 (a / t)) (fun _ => 1) (uIoo 0 a) := by
    intro t ht
    have ht' : t ∈ Ioo 0 a := by simpa [uIoo_of_le ha.le] using ht
    exact min_eq_left (one_le_div ht'.1 |>.2 ht'.2.le)
  have heq1 : EqOn (fun t : ℝ => min 1 (a / t)) (fun t => a * t⁻¹) (uIoo a 1) := by
    intro t ht
    have ht' : t ∈ Ioo a 1 := by simpa [uIoo_of_le ha1] using ht
    change min 1 (a / t) = a * t⁻¹
    rw [min_eq_right (div_le_one₀ (lt_trans ha ht'.1) |>.2 ht'.1.le), div_eq_mul_inv]
  have hi0 : IntervalIntegrable (fun t : ℝ => min 1 (a / t)) volume 0 a :=
    (intervalIntegrable_congr_uIoo heq0).2 intervalIntegrable_const
  have hi1 : IntervalIntegrable (fun t : ℝ => min 1 (a / t)) volume a 1 := by
    apply (intervalIntegrable_congr_uIoo heq1).2
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.const_mul
    apply continuousOn_inv₀.mono
    intro t ht
    have ht' : t ∈ Icc a 1 := by simpa [uIcc_of_le ha1] using ht
    simp only [mem_compl_iff, mem_singleton_iff]
    linarith [ht'.1]
  exact hi0.trans hi1

/-- The truncated kernel has a uniform integral bound over the unit interval. -/
theorem truncatedInvTime_integral_uniform {a s : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∫ t : ℝ in 0..1, min 1 (a / |t - s|)) ≤
      2 * (a * (1 + Real.log (1 / a))) := by
  let k : ℝ → ℝ := fun t => min 1 (a / t)
  have hi : IntervalIntegrable k volume 0 1 := truncatedInvTime_intervalIntegrable ha ha1
  have hsmall (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
      IntervalIntegrable k volume 0 u := by
    apply hi.mono_set
    simpa [uIcc_of_le hu0, uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
      (Icc_subset_Icc le_rfl hu1)
  have hiL : IntervalIntegrable (fun t => k (s - t)) volume 0 s := by
    have h := (hsmall s hs0 hs1).comp_sub_left s
    simpa using h.symm
  have hiR : IntervalIntegrable (fun t => k (t - s)) volume s 1 := by
    have h := (hsmall (1-s) (by linarith) (by linarith)).comp_sub_right s
    simpa using h
  have heqL : EqOn (fun t => k |t-s|) (fun t => k (s-t)) (uIoo 0 s) := by
    intro t ht
    have ht' : t ∈ Ioo 0 s := by simpa [uIoo_of_le hs0] using ht
    simp [abs_of_nonpos (show t-s ≤ 0 by linarith [ht'.2]), neg_sub]
  have heqR : EqOn (fun t => k |t-s|) (fun t => k (t-s)) (uIoo s 1) := by
    intro t ht
    have ht' : t ∈ Ioo s 1 := by simpa [uIoo_of_le hs1] using ht
    simp [abs_of_nonneg (show 0 ≤ t-s by linarith [ht'.1])]
  have hiL' := (intervalIntegrable_congr_uIoo heqL).2 hiL
  have hiR' := (intervalIntegrable_congr_uIoo heqR).2 hiR
  have hn : 0 ≤ᵐ[volume.restrict (Ioc 0 1)] k := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact le_min (by norm_num) (div_nonneg ha.le ht.1.le)
  have hbound (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
      (∫ t in 0..u, k t) ≤ a * (1 + Real.log (1 / a)) := by
    rw [← truncatedInvTime_integral ha ha1]
    exact intervalIntegral.integral_mono_interval le_rfl hu0 hu1 hn hi
  have hL : (∫ t in 0..s, k |t-s|) ≤ a * (1 + Real.log (1 / a)) := by
    rw [intervalIntegral.integral_congr_uIoo heqL,
      intervalIntegral.integral_comp_sub_left]
    simpa using hbound s hs0 hs1
  have hR : (∫ t in s..1, k |t-s|) ≤ a * (1 + Real.log (1 / a)) := by
    rw [intervalIntegral.integral_congr_uIoo heqR,
      intervalIntegral.integral_comp_sub_right]
    simpa using hbound (1-s) (by linarith) (by linarith)
  change (∫ t in 0..1, k |t-s|) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hiL' hiR']
  linarith

/-- The unit-time measure has a uniform truncated inverse-time kernel bound. -/
theorem truncatedInvTime_unit_time_lintegral_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (y : ℝ≥0) (hy : (y : ℝ) ≤ 1) :
    (∫⁻ t : ℝ≥0, min 1 (ENNReal.ofReal (a / |(t : ℝ) - (y : ℝ)|))
      ∂(Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) ≤
      ENNReal.ofReal (2 * (a * (1 + Real.log (1 / a)))) := by
  have hm : Measurable (fun t : ℝ≥0 =>
      min 1 (ENNReal.ofReal (a / |(t : ℝ) - (y : ℝ)|))) := by fun_prop
  rw [lintegral_map hm continuous_real_toNNReal.measurable]
  have heq : (∫⁻ t : ℝ, min 1
      (ENNReal.ofReal (a / |((Real.toNNReal t : ℝ≥0) : ℝ) - (y : ℝ)|))
      ∂(volume.restrict (Icc (0 : ℝ) 1))) =
      ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (min 1 (a / |t - (y : ℝ)|)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp [Real.toNNReal_of_nonneg ht.1, ENNReal.ofReal_min]
  rw [heq]
  let f : ℝ → ℝ := fun t => min 1 (a / |t - (y : ℝ)|)
  have hf0 : ∀ t, 0 ≤ f t := by
    intro t
    exact le_min (by norm_num) (div_nonneg ha.le (abs_nonneg _))
  have hfm : Measurable f := by dsimp [f]; fun_prop
  have hfi : IntegrableOn f (Icc (0 : ℝ) 1) := by
    apply IntegrableOn.of_bound (by simp) hfm.aestronglyMeasurable.restrict 1
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 t)]
    exact min_le_left _ _
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0)]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact truncatedInvTime_integral_uniform ha ha1 y.2 hy

/-- Unit-time occupation moments satisfy a logarithmic endpoint bound. -/
theorem planarBrownianMotion_occupation_moment_le_log_kernel (x z : ℂ) (n : ℕ) {r : ℝ} (hr : 0 < r)
    (ha1 : (2 / Real.pi) * (2 * r) ^ 2 ≤ 1) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    let a := (2 / Real.pi) * (2 * r) ^ 2
    (∫⁻ b : ContinuousPath ℂ, (ν {t | ‖b t - z‖ < r}) ^ (n + 1)
      ∂(planarBrownianMotion x)) ≤
      (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ≥0∞) *
        ENNReal.ofReal (2 * (a * (1 + Real.log (1 / a)))) ^ n := by
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let a : ℝ := (2 / Real.pi) * (2 * r) ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hp : IsProbabilityMeasure ν := by
    constructor
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := hp
  have hatom : NullSingletonClass ν := by
    constructor
    intro t
    dsimp [ν]
    rw [Measure.map_apply continuous_real_toNNReal.measurable (measurableSet_singleton t),
      Measure.restrict_apply (continuous_real_toNNReal.measurable (measurableSet_singleton t))]
    apply measure_mono_null _ (measure_singleton (t : ℝ))
    intro w hw
    have ht := congrArg (fun v : ℝ≥0 => (v : ℝ)) hw.1
    have hw0 : 0 ≤ w := hw.2.1
    simpa [Real.toNNReal_of_nonneg hw0] using ht
  let : NullSingletonClass ν := hatom
  have hs : ∀ᵐ y ∂ν, y ∈ Iic (1 : ℝ≥0) := by
    dsimp [ν]
    change ∀ᵐ y ∂(Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))), y ≤ 1
    apply (ae_map_iff continuous_real_toNNReal.measurable.aemeasurable
      (measurableSet_le measurable_id measurable_const)).2
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact Real.toNNReal_le_iff_le_coe.mpr (by simpa using hy.2)
  let k : ℝ≥0 → ℝ≥0 → ℝ≥0∞ :=
    fun t y => min 1 (ENNReal.ofReal (a / |(t : ℝ) - (y : ℝ)|))
  have hk : Measurable (fun p : ℝ≥0 × ℝ≥0 => k p.1 p.2) := by
    dsimp [k]; fun_prop
  have hK : ∀ y ∈ Iic (1 : ℝ≥0), (∫⁻ t, k t y ∂ν) ≤
      ENNReal.ofReal (2 * (a * (1 + Real.log (1 / a)))) := by
    intro y hy
    exact truncatedInvTime_unit_time_lintegral_le ha ha1 y (by exact_mod_cast hy)
  have h := planarBrownianMotion_occupation_moment_le_inv_time x z (n := n) hr.le ν
  have hh := lintegral_sum_chain_perm_prod_le ν k (Iic 1)
    (ENNReal.ofReal (2 * (a * (1 + Real.log (1 / a))))) hk hs hK n
  exact h.trans hh

end HarmonicBalls
