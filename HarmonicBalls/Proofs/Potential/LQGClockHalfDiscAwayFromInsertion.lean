import HarmonicBalls.Proofs.Potential.LQGClockAnnularFineFractionalMoment
import HarmonicBalls.Proofs.Potential.LQGClockAnnularStoppedUniformLimit
import HarmonicBalls.Proofs.Potential.LQGClockAnnularGlobalMeasurableLimit

/-! # Half-disc clocks for starts away from the insertion point

Planar Brownian motion started away from a point never visits it. On every finite time
interval such a path therefore stays at positive distance from the origin, and on that
interval the half-disc clock coincides with an annular clock at every smoothing scale.
Consequently the dyadic half-disc clocks of the inserted field converge locally uniformly
for every insertion strength `α`, without any moment condition on the insertion.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology Metric
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- A path that stays in the open disc of radius `R` up to time `t` has not left it by
time `t`. -/
theorem lt_exitTime_ball_of_forall_lt {c : ℂ} {R : ℝ} {b : ContinuousPath ℂ} {t : ℝ≥0}
    (h : ∀ s ≤ t, ‖b s - c‖ < R) :
    (t : ℝ≥0∞) < ContinuousPath.exitTime (ball c R) b := by
  by_contra hle
  obtain ⟨⟨s, hs⟩, hsU⟩ :=
    (ContinuousPath.exitTime_le_iff_mem_hitsSetBy (ball c R) isOpen_ball t b).mp (not_lt.mp hle)
  exact hsU (by rw [mem_ball, dist_eq_norm]; exact h s hs)

/-- A continuous path is bounded on every finite time interval. -/
theorem exists_nat_forall_norm_sub_lt (b : ContinuousPath ℂ) (c : ℂ) (t : ℝ≥0) :
    ∃ R : ℕ, ∀ s ≤ t, ‖b s - c‖ < R := by
  obtain ⟨M, hM⟩ := ((isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) t)).image
    (b.continuous.sub continuous_const).norm).bddAbove
  obtain ⟨R, hR⟩ := exists_nat_gt M
  exact ⟨R, fun s hs => (hM ⟨s, ⟨zero_le, hs⟩, rfl⟩).trans_lt hR⟩

/-- A continuous path avoiding a point stays at positive distance from it on every finite
time interval. -/
theorem exists_pos_le_norm_sub_of_forall_ne (b : ContinuousPath ℂ) {c : ℂ}
    (hb : ∀ t, b t ≠ c) (T : ℝ≥0) :
    ∃ d : ℝ, 0 < d ∧ ∀ s ≤ T, d ≤ ‖b s - c‖ := by
  obtain ⟨s₀, -, hmin⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T)).exists_isMinOn
    (nonempty_Icc.mpr zero_le) (b.continuous.sub continuous_const).norm.continuousOn
  exact ⟨‖b s₀ - c‖, norm_pos_iff.mpr (sub_ne_zero.mpr (hb s₀)),
    fun s hs => isMinOn_iff.mp hmin s ⟨zero_le, hs⟩⟩

/-- **Points are polar for planar Brownian motion.** Started away from `c`, the path never
visits `c`. -/
theorem ae_planarBrownianMotion_forall_ne {x c : ℂ} (hx : x ≠ c) :
    ∀ᵐ b ∂planarBrownianMotion x, ∀ t : ℝ≥0, b t ≠ c := by
  have hA : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hnull : ∀ R : ℝ, ‖x - c‖ < R → planarBrownianMotion x
      {b | ∃ t : ℝ≥0, b t = c ∧ (t : ℝ≥0∞) < ContinuousPath.exitTime (ball c R) b} = 0 := by
    intro R hAR
    have hbound : ∀ r : ℝ, r ∈ Ioo 0 ‖x - c‖ → planarBrownianMotion x
        {b | ∃ t : ℝ≥0, b t = c ∧ (t : ℝ≥0∞) < ContinuousPath.exitTime (ball c R) b} ≤
        ENNReal.ofReal ((Real.log R - Real.log ‖x - c‖) / (Real.log R - Real.log r)) := by
      rintro r ⟨hr, hrA⟩
      have hlog : 0 < Real.log R - Real.log r :=
        sub_pos.mpr (Real.log_lt_log hr (hrA.trans hAR))
      rw [ENNReal.ofReal_div_of_pos hlog]
      refine le_trans (measure_mono ?_)
        (planarBrownian_hit_closedBall_before_exit_le c hr hrA hAR le_rfl hAR)
      rintro b ⟨t, ht, hlt⟩
      exact ⟨t, by rw [ht, sub_self, norm_zero]; exact hr.le, hlt⟩
    have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal ((Real.log R - Real.log ‖x - c‖) /
        (Real.log R - Real.log r))) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun r : ℝ => Real.log R - Real.log r) (𝓝[>] 0) atTop := by
        simpa [sub_eq_add_neg] using tendsto_atTop_add_const_left _ (Real.log R)
          (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
      have h2 := h1.const_div_atTop (Real.log R - Real.log ‖x - c‖)
      have h3 := (ENNReal.continuous_ofReal.tendsto 0).comp h2
      rw [ENNReal.ofReal_zero] at h3
      exact h3
    refine le_antisymm (ge_of_tendsto hlim ?_) bot_le
    filter_upwards [Ioo_mem_nhdsGT hA] with r hr
    exact hbound r hr
  have hnat : ∀ n : ℕ, planarBrownianMotion x {b | ∃ t : ℝ≥0, b t = c ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (ball c (‖x - c‖ + 1 + n)) b} = 0 :=
    fun n => hnull _ (by have := n.cast_nonneg (α := ℝ); linarith)
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_iUnion_null hnat)
  intro b hb
  simp only [mem_ofPred_eq, not_forall, not_not] at hb
  obtain ⟨t, ht⟩ := hb
  obtain ⟨R, hR⟩ := exists_nat_forall_norm_sub_lt b c t
  refine mem_iUnion.mpr ⟨R, t, ht, lt_exitTime_ball_of_forall_lt fun s hs => (hR s hs).trans_le ?_⟩
  have := norm_nonneg (x - c)
  linarith

/-- **Half-disc clocks away from the insertion point.** For a start `x ≠ 0`, every
insertion strength `α` and `γ ^ 2 < 2`, the dyadic half-disc clocks of the inserted field
converge locally uniformly in time under the joint law, to a continuous nondecreasing
nonnegative limit. -/
theorem ae_exists_locally_uniform_limit_halfDiscClock_of_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {x : ℂ} (hx : x ≠ 0) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2) (α : ℝ) :
    ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ),
            {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                  (p.2 s.toNNReal)) - F t| < η := by
  have : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hdensity : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (fun z =>
      (dyadicScale (k+1))^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (k+1)) z)) := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec k
    have hc : Continuous (hcirc ω (dyadicScale (k+1))) := by
      rw [← funext (hω (dyadicScale (k+1)))]
      exact hHc ω (dyadicScale (k+1)) (dyadicScale_pos (k+1))
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (k+1)) z) =
        fun z => hcirc ω (dyadicScale (k+1)) z - hcirc ω 1 0 -
          α * Real.log (max (dyadicScale (k+1)) ‖z‖) := by
      funext z
      exact (hrec _ z (dyadicScale_pos (k+1))).symm
    have hci : Continuous (fun z =>
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (k+1)) z) := by
      rw [heq]
      exact (hc.sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log
          (fun _ => (lt_max_of_lt_left (dyadicScale_pos (k+1))).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hci))
  have hann : ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)), ∀ n : ℕ,
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ),
            {z : ℂ | 1 / ((n : ℝ) + 2) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale j)^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale j) z))
                  (p.2 s.toNNReal)) - F t| < η :=
    ae_all_iff.mpr fun n =>
      ae_exists_locally_uniform_limit_annularClock hh x hγ hγ2 α (by positivity)
  filter_upwards [hann,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hdensity,
    (Measure.quasiMeasurePreserving_snd (μ := P) (ν := planarBrownianMotion x)).ae
      (ae_planarBrownianMotion_forall_ne hx)] with p hp hc hne
  let f (j : ℕ) : ℂ → ℝ := fun z => (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z)
  let g (j : ℕ) (t : ℝ) : ℝ :=
    {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (f j) (p.2 t.toNNReal)
  let B (j : ℕ) (t : ℝ≥0) : ℝ := ∫ s in (0 : ℝ)..(t : ℝ), g j s
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
    obtain ⟨d, hd, hdist⟩ := exists_pos_le_norm_sub_of_forall_ne p.2 hne (N : ℝ≥0)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hd
    obtain ⟨G, -, -, -, hG⟩ := hp n
    refine ⟨G, fun η hη => ?_⟩
    filter_upwards [(tendsto_add_atTop_nat 1).eventually (hG N η hη)] with j hj t ht
    have heq : B j t = ∫ s in (0 : ℝ)..(t : ℝ),
        {z : ℂ | 1 / ((n : ℝ) + 2) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
              (p.2 s.toNNReal) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le t.coe_nonneg] at hs
      have hsN : s.toNNReal ≤ (N : ℝ≥0) :=
        (Real.toNNReal_le_iff_le_coe.mpr hs.2).trans ht
      have hfar : 1 / ((n : ℝ) + 2) ≤ ‖p.2 s.toNNReal‖ := by
        have h1 : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        have h2 := hdist _ hsN
        rw [sub_zero] at h2
        linarith
      show {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (f j) (p.2 s.toNNReal) =
        {z : ℂ | 1 / ((n : ℝ) + 2) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (f j) (p.2 s.toNNReal)
      by_cases hz : ‖p.2 s.toNNReal‖ ≤ 1 / 2
      · rw [Set.indicator_of_mem (show p.2 s.toNNReal ∈ {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
          from ⟨norm_nonneg _, hz⟩), Set.indicator_of_mem (show p.2 s.toNNReal ∈
          {z : ℂ | 1 / ((n : ℝ) + 2) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2} from ⟨hfar, hz⟩)]
      · rw [Set.indicator_of_notMem (show p.2 s.toNNReal ∉ {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
          from fun h => hz h.2), Set.indicator_of_notMem (show p.2 s.toNNReal ∉
          {z : ℂ | 1 / ((n : ℝ) + 2) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2} from fun h => hz h.2)]
    rw [heq]
    exact hj t ht
  exact exists_continuous_monotone_limit_of_uniform_on_nat_intervals B hBc hB0 hBm hnatB

/-- **Measurable half-disc clock away from the insertion point.** For a start `x ≠ 0`, every
insertion strength `α` and `γ ^ 2 < 2`, the dyadic half-disc clocks have a jointly
measurable locally uniform limit in field, path and time, with continuous nondecreasing
nonnegative time paths. -/
theorem exists_measurable_locally_uniform_limit_halfDiscClock_of_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {x : ℂ} (hx : x ≠ 0) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2) (α : ℝ) :
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
    filter_upwards [ae_exists_locally_uniform_limit_halfDiscClock_of_ne_zero hh hx hγ hγ2 α,
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

/-- **Measurable annular clock.** For every start, every insertion strength `α`, an inner
radius `δ > 0` and `γ ^ 2 < 2`, the dyadic annular clocks have a jointly measurable locally
uniform limit in field, path and time, with continuous nondecreasing nonnegative time
paths. -/
theorem exists_measurable_locally_uniform_limit_annularClock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable F ∧
      (∀ p, Continuous (fun t => F (p,t)) ∧ (∀ t, 0 ≤ F (p,t)) ∧
        Monotone (fun t => F (p,t))) ∧
      ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
        ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ),
            {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                  (p.2 s.toNNReal)) - F (p,t)| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, hHc, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let B : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
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
    filter_upwards [ae_exists_locally_uniform_limit_annularClock hh x hγ hγ2 α hδ,
      (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hAe]
      with p hp he
    obtain ⟨G, hGc, hG0, hGm, hG⟩ := hp
    refine ⟨G, hGc, hG0, hGm, ?_⟩
    intro T η hη
    filter_upwards [(tendsto_add_atTop_nat 1).eventually (hG T η hη)] with j hj t ht
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

end HarmonicBalls
