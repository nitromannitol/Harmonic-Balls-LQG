import HarmonicBalls.Proofs.Potential.UniformCauchyInMeasure
import HarmonicBalls.Proofs.Potential.LQGClockNearStart
import HarmonicBalls.Proofs.Potential.LQGClockEveryStart
import HarmonicBalls.Proofs.Potential.LQGActualApproximantPower

/-!
# LQG clocks from every start on one event of full probability

Write `A_k(b, t) = ∫_0^t ε_k^{γ²/2} e^{γ h_{ε_k}(b_s)} ds` (`lqgClockApprox`, `ε_k = 2^{-k}`) for the
dyadic approximations of the LQG clock along a path `b`. Fix a field `h` such that

* the circle averages `h_{ε_k}` are continuous;
* the approximate measures satisfy a ball bound `ν_k(B_s(z)) ≤ C s^β` for `‖z‖ ≤ R`,
  `0 < s ≤ r₀`, uniformly in `k` (for every `R`);
* from one start `x₀` the approximations are Cauchy in probability uniformly on bounded time
  intervals (for instance, there is an LQG clock from `x₀`).

Then from every start `x` there is an LQG clock (`forall_exists_isLQGClock_of_cauchy_one_start`).
Proof: for a small time `a > 0` and `j, k`, a path `b` with `sup_{t ≤ T} |A_j - A_k| ≥ η` has
`A_j(b, a) ≥ η/3`, or `A_k(b, a) ≥ η/3`, or the approximations of the shifted path `θ_a b`
differ by at least `η/3` before time `T`. The first two events have probability at most `θ/3`
for every `k` once `a` is small (`exists_pos_time_measure_clock_ge_le`). The law of `θ_a b`
under `P_x` is absolutely continuous with respect to its law under `P_{x₀}`, uniformly
(`planarBrownianMotion_map_shift_absolutelyContinuous`), and under `P_{x₀}` the shifted
approximations are Cauchy in probability; so the third event has probability at most `θ/3` for
large `j, k`. A sequence Cauchy in probability uniformly on bounded time sets has a limit
(`exists_tendsto_of_uniformCauchyInMeasure`), which is an LQG clock from `x`.

For a whole-plane GFF the first two properties hold almost surely
(`ae_continuous_fieldCircleAverage`, `IsWholePlaneGFF.ae_singular_approximant_ball_power_all_disks`),
so one LQG clock from one start gives, for almost every field, an LQG clock from every start
(`exists_ae_forall_isLQGClock_of_one_start`). This is the existence of a version of the clock
from every start on one event, which Garban-Rhodes-Vargas (2016, Theorem 2.7) prove for the
massive GFF by a coupling of Brownian paths; here every start comes from the Markov property at a
fixed time and the uniform ball bound.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Metric MarkovProcess
open scoped ENNReal NNReal

/-- Uniform absolute continuity of a finite measure with respect to a σ-finite one. -/
theorem exists_pos_lt_of_absolutelyContinuous {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
    [IsFiniteMeasure ν] [SigmaFinite μ] (h : ν ≪ μ) {θ : ℝ≥0∞} (hθ : θ ≠ 0) :
    ∃ δ > 0, ∀ s, MeasurableSet s → μ s < δ → ν s < θ := by
  obtain ⟨δ, hδ, hs⟩ := exists_pos_setLIntegral_lt_of_measure_lt (μ := μ) (f := ν.rnDeriv μ)
    ((Measure.lintegral_rnDeriv_le).trans_lt (measure_lt_top _ _)).ne hθ
  refine ⟨δ, hδ, fun s hsm hμs => ?_⟩
  have h1 := hs s hμs
  rwa [← withDensity_apply _ hsm, Measure.withDensity_rnDeriv_eq ν μ h] at h1

section Approximations

variable {γ : ℝ} {hε : ℝ → ℂ → ℝ}

/-- The approximate clocks are nonnegative. -/
theorem lqgClockApprox_dyadic_nonneg (k : ℕ) (w : ContinuousPath ℂ) (t : ℝ≥0) :
    0 ≤ lqgClockApprox γ hε (dyadicScale k) w t :=
  intervalIntegral.integral_nonneg (NNReal.coe_nonneg t) fun v _ =>
    dyadicIncrementIntegrand_nonneg γ hε k w v

/-- The approximate clocks are nondecreasing in time. -/
theorem lqgClockApprox_dyadic_mono {k : ℕ} (hc : Continuous (hε (dyadicScale k)))
    (w : ContinuousPath ℂ) {s t : ℝ≥0} (hst : s ≤ t) :
    lqgClockApprox γ hε (dyadicScale k) w s ≤ lqgClockApprox γ hε (dyadicScale k) w t := by
  have h := lqgClockApprox_sub_eq_dyadicIncrementApprox (γ := γ) hc w s t
  have h0 : 0 ≤ dyadicIncrementApprox γ hε k s t w :=
    intervalIntegral.integral_nonneg (by exact_mod_cast hst) fun v _ =>
      dyadicIncrementIntegrand_nonneg γ hε k w v
  linarith

/-- The approximate clock of the path shifted by `a` is the increment after time `a`. -/
theorem lqgClockApprox_dyadic_shift {k : ℕ} (hc : Continuous (hε (dyadicScale k)))
    (w : ContinuousPath ℂ) (a s : ℝ≥0) :
    lqgClockApprox γ hε (dyadicScale k) (ContinuousPath.shift a w) s =
      lqgClockApprox γ hε (dyadicScale k) w (a + s) - lqgClockApprox γ hε (dyadicScale k) w a := by
  rw [lqgClockApprox_sub_eq_dyadicIncrementApprox hc w a (a + s),
    dyadicIncrementApprox_shift γ hε k (a := (a : ℝ)) (b := ((a + s : ℝ≥0) : ℝ))
      (NNReal.coe_nonneg a) (by exact_mod_cast le_self_add) w,
    Real.toNNReal_coe, show ((a + s : ℝ≥0) : ℝ) - a = s by push_cast; ring]
  rfl

/-- The approximate clocks are continuous in time. -/
theorem continuous_lqgClockApprox_dyadic {k : ℕ} (hc : Continuous (hε (dyadicScale k)))
    (w : ContinuousPath ℂ) : Continuous (lqgClockApprox γ hε (dyadicScale k) w) := by
  have h : Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t,
      dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) (w s.toNNReal))) :=
    intervalIntegral.continuous_primitive (fun u v =>
      (continuous_dyadicIncrementIntegrand hc w).intervalIntegrable u v) 0
  exact h.comp NNReal.continuous_coe

/-- A measurable set between two levels of the supremum over `[0, T]` of the difference of two
approximate clocks: the supremum over the countable dense set of times `min (r⁺) T`, `r ∈ ℚ`. -/
theorem exists_measurableSet_sup_diff_between {j k : ℕ} (hcj : Continuous (hε (dyadicScale j)))
    (hck : Continuous (hε (dyadicScale k))) (T : ℝ≥0) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ M : Set (ContinuousPath ℂ), MeasurableSet M ∧
      {c | ∃ s ≤ T, 2 * ζ ≤ |lqgClockApprox γ hε (dyadicScale j) c s -
        lqgClockApprox γ hε (dyadicScale k) c s|} ⊆ M ∧
      M ⊆ {c | ∃ s ≤ T, ζ ≤ |lqgClockApprox γ hε (dyadicScale j) c s -
        lqgClockApprox γ hε (dyadicScale k) c s|} := by
  set f : ContinuousPath ℂ → ℝ≥0 → ℝ := fun c s =>
    lqgClockApprox γ hε (dyadicScale j) c s - lqgClockApprox γ hε (dyadicScale k) c s with hf
  refine ⟨⋃ r : ℚ, {c | ζ < |f c (min (Real.toNNReal r) T)|}, ?_, ?_, ?_⟩
  · refine MeasurableSet.iUnion fun r => measurableSet_lt measurable_const ?_
    exact continuous_abs.measurable.comp ((measurable_lqgClockApprox_time hcj _).sub
      (measurable_lqgClockApprox_time hck _))
  · rintro c ⟨s, hsT, hs⟩
    have hfc : Continuous (f c) :=
      (continuous_lqgClockApprox_dyadic hcj c).sub (continuous_lqgClockApprox_dyadic hck c)
    have hs' : ζ < |f c s| := lt_of_lt_of_le (by linarith : ζ < 2 * ζ) hs
    have hev : ∀ᶠ t in 𝓝 s, ζ < |f c t| :=
      (continuous_abs.comp hfc).continuousAt.eventually (lt_mem_nhds hs')
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨r, hsr, hrs⟩ := exists_rat_btwn (show (s : ℝ) < s + δ by linarith)
    have hr0 : (0 : ℝ) ≤ r := (NNReal.coe_nonneg s).trans hsr.le
    refine mem_iUnion.2 ⟨r, ?_⟩
    show ζ < |f c (min (Real.toNNReal r) T)|
    refine hball ?_
    rw [NNReal.dist_eq]
    rcases le_total (Real.toNNReal r) T with hle | hle
    · rw [min_eq_left hle, Real.coe_toNNReal _ hr0, abs_lt]
      constructor <;> linarith
    · rw [min_eq_right hle, abs_lt]
      have : (T : ℝ) ≤ r := by
        have := (NNReal.coe_le_coe.2 hle)
        rwa [Real.coe_toNNReal _ hr0] at this
      have hsT' : (s : ℝ) ≤ T := by exact_mod_cast hsT
      constructor <;> linarith
  · intro c hc
    obtain ⟨r, hr⟩ := mem_iUnion.1 hc
    exact ⟨min (Real.toNNReal r) T, min_le_right _ _, hr.le⟩

/-- The approximations are Cauchy in probability uniformly on bounded time sets if they converge
to an LQG clock. -/
theorem cauchy_of_isLQGClock {x : ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : IsLQGClock planarBrownianMotion γ hε x F) (T : ℝ≥0) {η : ℝ} (hη : 0 < η) {θ : ℝ}
    (hθ : 0 < θ) : ∃ N : ℕ, ∀ j, N ≤ j → ∀ k, N ≤ k →
      planarBrownianMotion x {b | ∃ t ≤ T, η ≤ |lqgClockApprox γ hε (dyadicScale j) b t -
        lqgClockApprox γ hε (dyadicScale k) b t|} ≤ ENNReal.ofReal θ := by
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.1 (hF T (η / 2) (by positivity))
    (ENNReal.ofReal (θ / 2)) (by simp; positivity)
  refine ⟨N, fun j hj k hk => ?_⟩
  have hsub : {b | ∃ t ≤ T, η ≤ |lqgClockApprox γ hε (dyadicScale j) b t -
      lqgClockApprox γ hε (dyadicScale k) b t|} ⊆
      {b | ∃ t ≤ T, η / 2 ≤ |lqgClockApprox γ hε (dyadicScale j) b t - F b t|} ∪
      {b | ∃ t ≤ T, η / 2 ≤ |lqgClockApprox γ hε (dyadicScale k) b t - F b t|} := by
    rintro b ⟨t, htT, hb⟩
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_exists, not_and, not_le] at hnot
    have h1 := hnot.1 t htT
    have h2 := hnot.2 t htT
    have h3 : |lqgClockApprox γ hε (dyadicScale j) b t - lqgClockApprox γ hε (dyadicScale k) b t| ≤
        |lqgClockApprox γ hε (dyadicScale j) b t - F b t| +
          |lqgClockApprox γ hε (dyadicScale k) b t - F b t| := by
      rw [show lqgClockApprox γ hε (dyadicScale j) b t - lqgClockApprox γ hε (dyadicScale k) b t =
        (lqgClockApprox γ hε (dyadicScale j) b t - F b t) -
          (lqgClockApprox γ hε (dyadicScale k) b t - F b t) by ring]
      exact abs_sub _ _
    linarith
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) := add_le_add (hN j hj) (hN k hk)
    _ = ENNReal.ofReal θ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

/-- **After a fixed time, Cauchy in probability from one start gives Cauchy in probability from
every start** for the approximations of the shifted path. -/
theorem exists_index_shift_diff_le (hc : ∀ k, Continuous (hε (dyadicScale k))) {x₀ : ℂ}
    (hcauchy : ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ θ : ℝ, 0 < θ → ∃ N : ℕ, ∀ j, N ≤ j → ∀ k, N ≤ k →
      planarBrownianMotion x₀ {b | ∃ t ≤ T, η ≤ |lqgClockApprox γ hε (dyadicScale j) b t -
        lqgClockApprox γ hε (dyadicScale k) b t|} ≤ ENNReal.ofReal θ)
    {a : ℝ≥0} (ha : 0 < a) (x : ℂ) (T : ℝ≥0) {ζ θ : ℝ} (hζ : 0 < ζ) (hθ : 0 < θ) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ k, N ≤ k → planarBrownianMotion x
      {b | ∃ s ≤ T, 2 * ζ ≤ |lqgClockApprox γ hε (dyadicScale j) (ContinuousPath.shift a b) s -
        lqgClockApprox γ hε (dyadicScale k) (ContinuousPath.shift a b) s|} ≤ ENNReal.ofReal θ := by
  have hsh : Measurable (ContinuousPath.shift a : ContinuousPath ℂ → ContinuousPath ℂ) :=
    ContinuousPath.measurable_shift_fixed a
  have hac := planarBrownianMotion_map_shift_absolutelyContinuous ha x x₀
  obtain ⟨δ, hδ, hδs⟩ := exists_pos_lt_of_absolutelyContinuous hac (θ := ENNReal.ofReal θ)
    (by simpa using hθ)
  obtain ⟨δ', hδ'0, hδ'δ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hδ
  obtain ⟨N, hN⟩ := hcauchy (a + T) (ζ / 2) (by positivity) (δ' : ℝ) (by exact_mod_cast hδ'0)
  refine ⟨N, fun j hj k hk => ?_⟩
  obtain ⟨M, hMm, hBM, hMB⟩ := exists_measurableSet_sup_diff_between (γ := γ) (hc j) (hc k) T hζ
  have hpre : ContinuousPath.shift a ⁻¹' M ⊆ {b | ∃ t ≤ a + T, ζ / 2 ≤
      |lqgClockApprox γ hε (dyadicScale j) b t - lqgClockApprox γ hε (dyadicScale k) b t|} := by
    intro b hb
    obtain ⟨s, hsT, hs⟩ := hMB hb
    rw [lqgClockApprox_dyadic_shift (hc j), lqgClockApprox_dyadic_shift (hc k)] at hs
    by_contra hnot
    simp only [mem_ofPred_eq, not_exists, not_and, not_le] at hnot
    have h1 := hnot (a + s) (add_le_add le_rfl hsT)
    have h2 := hnot a le_self_add
    have h3 : |lqgClockApprox γ hε (dyadicScale j) b (a + s) - lqgClockApprox γ hε (dyadicScale j) b a -
        (lqgClockApprox γ hε (dyadicScale k) b (a + s) - lqgClockApprox γ hε (dyadicScale k) b a)| ≤
        |lqgClockApprox γ hε (dyadicScale j) b (a + s) - lqgClockApprox γ hε (dyadicScale k) b (a + s)| +
          |lqgClockApprox γ hε (dyadicScale j) b a - lqgClockApprox γ hε (dyadicScale k) b a| := by
      rw [show lqgClockApprox γ hε (dyadicScale j) b (a + s) - lqgClockApprox γ hε (dyadicScale j) b a -
          (lqgClockApprox γ hε (dyadicScale k) b (a + s) - lqgClockApprox γ hε (dyadicScale k) b a) =
          (lqgClockApprox γ hε (dyadicScale j) b (a + s) -
            lqgClockApprox γ hε (dyadicScale k) b (a + s)) -
          (lqgClockApprox γ hε (dyadicScale j) b a - lqgClockApprox γ hε (dyadicScale k) b a) by ring]
      exact abs_sub _ _
    linarith
  have hν₀ : (planarBrownianMotion x₀).map (ContinuousPath.shift a) M < δ := by
    rw [Measure.map_apply hsh hMm]
    exact lt_of_le_of_lt ((measure_mono hpre).trans (hN j hj k hk))
      (by rwa [ENNReal.ofReal_coe_nnreal])
  have hν := hδs M hMm hν₀
  rw [Measure.map_apply hsh hMm] at hν
  have hsub2 : {b | ∃ s ≤ T, 2 * ζ ≤
      |lqgClockApprox γ hε (dyadicScale j) (ContinuousPath.shift a b) s -
        lqgClockApprox γ hε (dyadicScale k) (ContinuousPath.shift a b) s|} ⊆
      ContinuousPath.shift a ⁻¹' M := fun b hb => hBM hb
  exact (measure_mono hsub2).trans hν.le

end Approximations

/-- **LQG clocks from every start for one field**, from the continuity of the circle averages, a
ball bound on the approximate measures uniform in the scale and the centre, and Cauchy
convergence in probability of the approximations from one start. -/
theorem forall_exists_isLQGClock_of_cauchy_one_start {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    (hc : ∀ k, Continuous (hε (dyadicScale k)))
    (hball : ∀ R : ℝ, ∃ C β r₀ : ℝ, 0 < C ∧ 0 < β ∧ 0 < r₀ ∧ ∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ R →
      ∀ s : ℝ, 0 < s → s ≤ r₀ → lqgApprox γ hε (dyadicScale k) (ball z s) ≤ ENNReal.ofReal (C * s ^ β))
    {x₀ : ℂ}
    (hcauchy : ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ θ : ℝ, 0 < θ → ∃ N : ℕ, ∀ j, N ≤ j → ∀ k, N ≤ k →
      planarBrownianMotion x₀ {b | ∃ t ≤ T, η ≤ |lqgClockApprox γ hε (dyadicScale j) b t -
        lqgClockApprox γ hε (dyadicScale k) b t|} ≤ ENNReal.ofReal θ)
    (x : ℂ) : ∃ F, IsLQGClock planarBrownianMotion γ hε x F := by
  refine (exists_tendsto_of_uniformCauchyInMeasure (planarBrownianMotion x)
    (fun k b t => lqgClockApprox γ hε (dyadicScale k) b t) ?_).imp fun F hF T η hη => hF T η hη
  intro T η hη θ hθ
  obtain ⟨C, β, r₀, hC, hβ, hr₀, hb⟩ := hball ‖x‖
  obtain ⟨a, ha, hsmall⟩ := exists_pos_time_measure_clock_ge_le (x := x)
    (g := fun k z => dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) z))
    (fun k => continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hc k))))
    (fun k z => mul_nonneg (Real.rpow_nonneg (dyadicScale_pos k).le _) (Real.exp_pos _).le)
    hC hβ hr₀ (fun k t ht htr => hb k x le_rfl t ht htr.le) (η := η / 3) (θ := θ / 3)
    (by positivity) (by positivity)
  obtain ⟨N, hN⟩ := exists_index_shift_diff_le hc hcauchy ha x T (ζ := η / 6) (θ := θ / 3)
    (by positivity) (by positivity)
  refine ⟨N, fun j hj k hk => ?_⟩
  have hsub : {b | ∃ t ≤ T, η ≤ |lqgClockApprox γ hε (dyadicScale j) b t -
      lqgClockApprox γ hε (dyadicScale k) b t|} ⊆
      ({b | η / 3 ≤ lqgClockApprox γ hε (dyadicScale j) b a} ∪
        {b | η / 3 ≤ lqgClockApprox γ hε (dyadicScale k) b a}) ∪
      {b | ∃ s ≤ T, 2 * (η / 6) ≤
        |lqgClockApprox γ hε (dyadicScale j) (ContinuousPath.shift a b) s -
          lqgClockApprox γ hε (dyadicScale k) (ContinuousPath.shift a b) s|} := by
    rintro b ⟨t, htT, hηt⟩
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_exists, not_and, not_le] at hnot
    obtain ⟨⟨hAj, hAk⟩, hsh⟩ := hnot
    have h5 := lqgClockApprox_dyadic_nonneg (γ := γ) (hε := hε) j b a
    have h6 := lqgClockApprox_dyadic_nonneg (γ := γ) (hε := hε) k b a
    rcases le_or_gt t a with hta | hat
    · have h1 := lqgClockApprox_dyadic_mono (γ := γ) (hc j) b hta
      have h2 := lqgClockApprox_dyadic_mono (γ := γ) (hc k) b hta
      have h3 := lqgClockApprox_dyadic_nonneg (γ := γ) (hε := hε) j b t
      have h4 := lqgClockApprox_dyadic_nonneg (γ := γ) (hε := hε) k b t
      have : |lqgClockApprox γ hε (dyadicScale j) b t - lqgClockApprox γ hε (dyadicScale k) b t| < η :=
        abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
      linarith
    · have hs : a + (t - a) = t := add_tsub_cancel_of_le hat.le
      have hsT : t - a ≤ T := tsub_le_iff_right.2 (htT.trans le_self_add)
      have h7 := hsh (t - a) hsT
      rw [lqgClockApprox_dyadic_shift (hc j), lqgClockApprox_dyadic_shift (hc k), hs] at h7
      have : |lqgClockApprox γ hε (dyadicScale j) b t - lqgClockApprox γ hε (dyadicScale k) b t| < η := by
        rw [abs_lt] at h7 ⊢
        constructor <;> linarith
      linarith
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ (ENNReal.ofReal (θ / 3) + ENNReal.ofReal (θ / 3)) + ENNReal.ofReal (θ / 3) :=
        add_le_add ((measure_union_le _ _).trans (add_le_add (hsmall j) (hsmall k))) (hN j hj k hk)
    _ = ENNReal.ofReal θ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **LQG clocks from every start on one event**: for a whole-plane GFF, `0 < γ < 2` and
`α < Q`, if the approximations of the clock of the inserted field are almost surely Cauchy in
probability from one start, then for almost every field there is an LQG clock from every start. -/
theorem ae_forall_exists_isLQGClock_of_cauchy {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ) {x₀ : ℂ}
    (hcauchy : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ θ : ℝ, 0 < θ → ∃ N : ℕ, ∀ j, N ≤ j →
      ∀ k, N ≤ k → planarBrownianMotion x₀ {b | ∃ t ≤ T, η ≤
        |lqgClockApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale j) b t -
          lqgClockApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k) b t|} ≤
        ENNReal.ofReal θ) :
    ∀ᵐ ω ∂P, ∀ x : ℂ, ∃ F, IsLQGClock planarBrownianMotion γ (fieldCircleAverage α (hcirc ω)) x F := by
  filter_upwards [hh.ae_singular_approximant_ball_power_all_disks hγ hγ2 hα,
    ae_continuous_fieldCircleAverage ((LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh) α, hcauchy]
    with ω hball hc hω x
  exact forall_exists_isLQGClock_of_cauchy_one_start (fun k => hc _ (dyadicScale_pos k)) hball hω x

/-- **A version of the LQG clock from every start**: for a whole-plane GFF, `0 < γ < 2` and
`α < Q`, an LQG clock of the inserted field from one start gives a family `F` of clocks with,
for almost every field, `F ω x` an LQG clock from `x` for every start `x`. -/
theorem exists_ae_forall_isLQGClock_of_one_start {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ) {x₀ : ℂ} {F₀ : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF₀ : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ (fieldCircleAverage α (hcirc ω)) x₀ (F₀ ω)) :
    ∃ F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ, ∀ᵐ ω ∂P, ∀ x : ℂ,
      IsLQGClock planarBrownianMotion γ (fieldCircleAverage α (hcirc ω)) x (F ω x) := by
  have hall := ae_forall_exists_isLQGClock_of_cauchy hh hγ hγ2 hα (x₀ := x₀)
    (hF₀.mono fun ω hω T η hη θ hθ => cauchy_of_isLQGClock hω T hη hθ)
  refine ⟨fun ω x => Classical.epsilon fun F => IsLQGClock planarBrownianMotion γ
    (fieldCircleAverage α (hcirc ω)) x F, ?_⟩
  filter_upwards [hall] with ω hω x
  exact Classical.epsilon_spec (hω x)

end HarmonicBalls
