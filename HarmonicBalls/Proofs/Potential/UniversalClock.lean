import HarmonicBalls.Defs.LBM

/-!
# One clock for all starting points

Let `a_k(b, t)` be approximate clocks of a path `b` (measurable in `b`, continuous, nondecreasing
and zero at time zero in `t`, additive under time shifts, `IsApproxClocks`), and let `F x` be, for
every start `x` in a set `K₀`, a limit of `a_k` in `Q x`-probability uniformly on compact time
intervals (`TendstoClockInMeasure`). This module builds one measurable functional `A` with
`A = F x` almost surely under `Q x` for every `x ∈ K₀` (`exists_universal_clock`), under two
hypotheses: for almost every start of a reference law `ρ` the approximations have a limit, and
events holding almost surely from `ρ`-almost every start hold, from every `x ∈ K₀`, for the path
shifted by any positive time (the Markov property).

* Under the mixture `Q ∘ₘ ρ` the approximations are Cauchy in probability, so along one
  subsequence `k_j` they are almost surely Cauchy, uniformly on compact time intervals.
* By the Markov hypothesis, for every `x ∈ K₀` and `s > 0`, the increments
  `a_{k_j}(b, t) - a_{k_j}(b, s ∧ t) = a_{k_j}(θ_s b, t - s)` converge almost surely.
* `A(t, b) = sup_n lim_j (a_{k_j}(b, t) - a_{k_j}(b, s_n ∧ t))`, `s_n = 1/(n + 1)`. Along a further
  subsequence `a_{k_j} → F x` almost surely (`ae_tendsto_of_tendstoClockInMeasure`), so the inner
  limits are `F x(t) - F x(s_n ∧ t)`, and the supremum is `F x(t)` since `F x` is continuous,
  nondecreasing and vanishes at zero.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

/-- `a` converges to `F` in `μ`-probability, uniformly on compact time intervals. For
`a k = lqgClockApprox γ hε (dyadicScale k)` and `μ = Q x` this is `IsLQGClock Q γ hε x F`. -/
def TendstoClockInMeasure (μ : Measure (ContinuousPath ℂ))
    (a : ℕ → ContinuousPath ℂ → ℝ≥0 → ℝ) (F : ContinuousPath ℂ → ℝ≥0 → ℝ) : Prop :=
  ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
    Tendsto (fun k : ℕ => μ {b | ∃ t ≤ T, η ≤ |a k b t - F b t|}) atTop (𝓝 0)

theorem isLQGClock_iff_tendstoClockInMeasure {Q : Kernel ℂ (ContinuousPath ℂ)} {γ : ℝ}
    {hε : ℝ → ℂ → ℝ} {x : ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ} :
    IsLQGClock Q γ hε x F ↔
      TendstoClockInMeasure (Q x) (fun k => lqgClockApprox γ hε (dyadicScale k)) F :=
  Iff.rfl

/-- Approximate clocks: measurable in the path, continuous and nondecreasing in time, zero at
time zero, and additive under the time shift. -/
structure IsApproxClocks (a : ℕ → ContinuousPath ℂ → ℝ≥0 → ℝ) : Prop where
  measurable : ∀ k t, Measurable fun b => a k b t
  continuous : ∀ k b, Continuous (a k b)
  monotone : ∀ k b, Monotone (a k b)
  map_zero : ∀ k b, a k b 0 = 0
  shift : ∀ k b s t, a k b (s + t) = a k b s + a k (ContinuousPath.shift s b) t

/-- **A limit in probability is an almost sure limit along a subsequence**: for any sequence of
indices `k → ∞` there are indices `φ → ∞` with `a_{k(φ i)} → F` at all times, almost surely; then
`F` is almost surely zero at zero, continuous and nondecreasing. -/
theorem ae_tendsto_of_tendstoClockInMeasure {μ : Measure (ContinuousPath ℂ)}
    {a : ℕ → ContinuousPath ℂ → ℝ≥0 → ℝ} (ha : IsApproxClocks a)
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hF : TendstoClockInMeasure μ a F)
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) :
    ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧ ∀ᵐ b ∂μ,
      (∀ t, Tendsto (fun i => a (k (φ i)) b t) atTop (𝓝 (F b t))) ∧
      F b 0 = 0 ∧ Continuous (F b) ∧ Monotone (F b) := by
  let S : ℕ → ℕ → Set (ContinuousPath ℂ) := fun j m =>
    {b | ∃ t ≤ (j : ℝ≥0), 1 / ((j : ℝ) + 1) ≤ |a m b t - F b t|}
  have hsmall (j : ℕ) : ∃ i, j ≤ i ∧ μ (S j (k i)) < ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
    have h := (hF (j : ℝ≥0) (1 / ((j : ℝ) + 1)) (by positivity)).comp hk
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ((1 / 2 : ℝ) ^ j) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    obtain ⟨i, hi⟩ := ((h.eventually (gt_mem_nhds hpos)).and (eventually_ge_atTop j)).exists
    exact ⟨i, hi.2, hi.1⟩
  choose φ hφj hφ using hsmall
  refine ⟨φ, tendsto_atTop_mono hφj tendsto_id, ?_⟩
  have hsum : (∑' j, μ (S j (k (φ j)))) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun j => (hφ j).le)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with b hb
  have hclose : ∀ᶠ j : ℕ in atTop, ∀ t : ℝ≥0, t ≤ (j : ℝ≥0) →
      |a (k (φ j)) b t - F b t| < 1 / ((j : ℝ) + 1) := by
    filter_upwards [hb] with j hj t ht
    by_contra h
    exact hj ⟨t, ht, not_lt.mp h⟩
  have hsmallj : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hunif (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ j : ℕ in atTop, ∀ t : ℝ≥0, t ≤ T → |a (k (φ j)) b t - F b t| < ε := by
    obtain ⟨N, hN⟩ := exists_nat_ge T
    filter_upwards [hclose, hsmallj.eventually (gt_mem_nhds hε),
      eventually_ge_atTop N] with j hj hjε hjN t ht
    exact (hj t (ht.trans (hN.trans (by exact_mod_cast hjN)))).trans hjε
  have hpt (t : ℝ≥0) : Tendsto (fun j => a (k (φ j)) b t) atTop (𝓝 (F b t)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := (hunif t ε hε).exists_forall_of_atTop
    exact ⟨N, fun j hj => by rw [Real.dist_eq]; exact hN j hj t le_rfl⟩
  refine ⟨hpt, ?_, ?_, ?_⟩
  · have h := hpt 0
    simp only [ha.map_zero] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  · have hloc : TendstoLocallyUniformly (fun j => a (k (φ j)) b) (F b) atTop := by
      rw [tendstoLocallyUniformly_iff_forall_isCompact]
      intro K hK
      obtain ⟨T, hT⟩ := hK.bddAbove
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [hunif T ε hε] with j hj t ht
      rw [Real.dist_eq, abs_sub_comm]
      exact hj t (hT ht)
    exact hloc.continuous (Filter.Eventually.frequently (Filter.Eventually.of_forall fun j =>
      ha.continuous _ b))
  · intro s t hst
    exact le_of_tendsto_of_tendsto' (hpt s) (hpt t) fun j => ha.monotone _ b hst

/-- A value of a continuous function above a level at a time `t ≤ T` is attained above the level
at a rational time `q ≤ T`. -/
theorem exists_rat_le_of_lt {f : ℝ≥0 → ℝ} (hf : Continuous f) {T t : ℝ≥0} (ht : t ≤ T) {η : ℝ}
    (h : η < f t) : ∃ q : ℚ, 0 ≤ q ∧ (q : ℝ) ≤ T ∧ η < f (q : ℝ).toNNReal := by
  rcases (zero_le : (0 : ℝ≥0) ≤ t).eq_or_lt with h0 | h0
  · refine ⟨0, le_rfl, by simp, ?_⟩
    rw [← h0] at h
    simpa using h
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hf.continuousAt (f t - η) (by linarith)
  have ht0 : (0 : ℝ) < t := by exact_mod_cast h0
  have hlo : max ((t : ℝ) - δ) 0 < t := max_lt (by linarith) ht0
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlo
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (le_max_right _ _) hr1
  have hrδ : (t : ℝ) - δ < r := lt_of_le_of_lt (le_max_left _ _) hr1
  refine ⟨r, by exact_mod_cast hr0.le, hr2.le.trans (by exact_mod_cast ht), ?_⟩
  have hd : dist (r : ℝ).toNNReal t < δ := by
    rw [NNReal.dist_eq, Real.coe_toNNReal _ hr0.le, abs_lt]
    constructor <;> linarith
  have := hball hd
  rw [Real.dist_eq, abs_lt] at this
  linarith [this.1]

/-- A sequence with `|u j - u (j + 1)| ≤ 2⁻ʲ` from some index on converges. -/
theorem exists_tendsto_of_eventually_abs_sub_le {u : ℕ → ℝ} {J : ℕ}
    (h : ∀ j ≥ J, |u j - u (j + 1)| ≤ (1 / 2 : ℝ) ^ j) : ∃ L, Tendsto u atTop (𝓝 L) := by
  have hc : CauchySeq fun n => u (n + J) := by
    refine cauchySeq_of_le_geometric (1 / 2 : ℝ) 1 (by norm_num) fun n => ?_
    rw [Real.dist_eq, show n + 1 + J = n + J + 1 by ring]
    calc |u (n + J) - u (n + J + 1)| ≤ (1 / 2 : ℝ) ^ (n + J) := h _ (Nat.le_add_left J n)
      _ ≤ 1 * (1 / 2 : ℝ) ^ n := by
        rw [one_mul, pow_add]
        exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨L, (tendsto_add_atTop_iff_nat J).1 hL⟩

/-- The rational Cauchy event: `η < |a_k(q) - a_m(q)|` at some rational time `0 ≤ q ≤ T`. -/
def clockCauchyEvent (a : ℕ → ContinuousPath ℂ → ℝ≥0 → ℝ) (k m T : ℕ) (η : ℝ) :
    Set (ContinuousPath ℂ) :=
  ⋃ q : ℚ, {b | 0 ≤ q ∧ (q : ℝ) ≤ T ∧ η < |a k b (q : ℝ).toNNReal - a m b (q : ℝ).toNNReal|}

theorem measurableSet_clockCauchyEvent {a : ℕ → ContinuousPath ℂ → ℝ≥0 → ℝ}
    (ha : IsApproxClocks a) (k m T : ℕ) (η : ℝ) : MeasurableSet (clockCauchyEvent a k m T η) := by
  refine MeasurableSet.iUnion fun q => ?_
  simp only [ofPred_and]
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    (measurableSet_lt measurable_const
      (continuous_abs.measurable.comp ((ha.measurable k _).sub (ha.measurable m _)))))

/-- The Cauchy event is controlled by the distance to any limit. -/
theorem measure_clockCauchyEvent_le {μ : Measure (ContinuousPath ℂ)}
    {a : ℕ → ContinuousPath ℂ → ℝ≥0 → ℝ} (G : ContinuousPath ℂ → ℝ≥0 → ℝ) (k m T : ℕ) (η : ℝ) :
    μ (clockCauchyEvent a k m T η) ≤
      μ {b | ∃ t ≤ (T : ℝ≥0), η / 2 ≤ |a k b t - G b t|} +
        μ {b | ∃ t ≤ (T : ℝ≥0), η / 2 ≤ |a m b t - G b t|} := by
  refine (measure_mono fun b hb => ?_).trans (measure_union_le _ _)
  obtain ⟨q, hq0, hqT, hq⟩ := mem_iUnion.1 hb
  have hqT' : (q : ℝ).toNNReal ≤ (T : ℝ≥0) := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_natCast]
    exact hqT
  by_contra hcon
  simp only [mem_union, mem_ofPred_eq, not_or, not_exists, not_and, not_le] at hcon
  have h1 := hcon.1 _ hqT'
  have h2 := hcon.2 _ hqT'
  have := abs_sub_le (a k b (q : ℝ).toNNReal) (G b (q : ℝ).toNNReal) (a m b (q : ℝ).toNNReal)
  rw [abs_sub_comm (G b _)] at this
  linarith

theorem tendsto_iSup_add_of_tendsto_zero {u : ℕ → ℝ≥0∞} (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun K => ⨆ k : ℕ, u (K + k)) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero] at hu ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu ε hε)
  filter_upwards [eventually_ge_atTop N] with K hK
  exact iSup_le fun k => hN _ (hK.trans (Nat.le_add_right K k))

/-- **One clock for all starting points.** -/
theorem exists_universal_clock {Q : Kernel ℂ (ContinuousPath ℂ)} [IsMarkovKernel Q]
    {ρ : Measure ℂ} [IsProbabilityMeasure ρ] {a : ℕ → ContinuousPath ℂ → ℝ≥0 → ℝ}
    (ha : IsApproxClocks a) {K₀ : Set ℂ} {F : ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : ∀ x ∈ K₀, TendstoClockInMeasure (Q x) a (F x))
    (href : ∀ᵐ w ∂ρ, ∃ G, TendstoClockInMeasure (Q w) a G)
    (htr : ∀ x ∈ K₀, ∀ s : ℝ≥0, 0 < s → ∀ S : Set (ContinuousPath ℂ), MeasurableSet S →
      (∀ᵐ w ∂ρ, ∀ᵐ b ∂(Q w), b ∈ S) → ∀ᵐ b ∂(Q x), ContinuousPath.shift s b ∈ S) :
    ∃ A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, (∀ t, Measurable (A t)) ∧
      (∀ m : ℝ≥0 → MeasurableSpace (ContinuousPath ℂ), Monotone m →
        (∀ k t, Measurable[m t] fun b => a k b t) → ∀ t, Measurable[m t] (A t)) ∧
      ∀ x ∈ K₀, ∀ r : ℝ≥0, ∀ᵐ b ∂(Q x), ∀ u,
        (A u (ContinuousPath.shift r b) : ℝ) = F x b (r + u) - F x b r := by
  -- the tail suprema of the Cauchy probabilities tend to zero in mean under `ρ`
  let e : ℕ → ℕ → ℂ → ℝ≥0∞ := fun j K w =>
    ⨆ k : ℕ, ⨆ m : ℕ, Q w (clockCauchyEvent a (K + k) (K + m) j ((1 / 2 : ℝ) ^ j))
  have he_meas : ∀ j K, Measurable (e j K) := fun j K =>
    Measurable.iSup fun k => Measurable.iSup fun m =>
      Q.measurable_coe (measurableSet_clockCauchyEvent ha _ _ _ _)
  have he_lim : ∀ j, Tendsto (fun K => ∫⁻ w, e j K w ∂ρ) atTop (𝓝 0) := by
    intro j
    have h := tendsto_lintegral_of_dominated_convergence (μ := ρ) (fun _ => (1 : ℝ≥0∞)) (he_meas j)
      (fun K => Eventually.of_forall fun w => iSup_le fun k => iSup_le fun m => prob_le_one)
      (by simp) (f := fun _ => 0) (by
        filter_upwards [href] with w ⟨G, hG⟩
        have hb := hG (j : ℝ≥0) ((1 / 2 : ℝ) ^ j / 2) (by positivity)
        have hsup := tendsto_iSup_add_of_tendsto_zero hb
        have h2 : Tendsto (fun K => (⨆ k : ℕ, (Q w) {b | ∃ t ≤ (j : ℝ≥0),
            (1 / 2 : ℝ) ^ j / 2 ≤ |a (K + k) b t - G b t|}) + ⨆ k : ℕ, (Q w) {b | ∃ t ≤ (j : ℝ≥0),
            (1 / 2 : ℝ) ^ j / 2 ≤ |a (K + k) b t - G b t|}) atTop (𝓝 0) := by
          have := hsup.add hsup
          rwa [add_zero] at this
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
          (fun K => zero_le) fun K => ?_
        refine iSup_le fun k => iSup_le fun m => (measure_clockCauchyEvent_le G _ _ _ _).trans ?_
        exact add_le_add (le_iSup (fun k => (Q w) {b | ∃ t ≤ (j : ℝ≥0),
          (1 / 2 : ℝ) ^ j / 2 ≤ |a (K + k) b t - G b t|}) k)
          (le_iSup (fun k => (Q w) {b | ∃ t ≤ (j : ℝ≥0),
          (1 / 2 : ℝ) ^ j / 2 ≤ |a (K + k) b t - G b t|}) m))
    simpa using h
  -- choose the indices
  have hK : ∀ j, ∃ K, j ≤ K ∧ ∫⁻ w, e j K w ∂ρ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
    intro j
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := ENNReal.ofReal_pos.2 (by positivity)
    obtain ⟨K, hK⟩ := (((he_lim j).eventually (ge_mem_nhds hpos)).and
      (eventually_ge_atTop j)).exists
    exact ⟨K, hK.2, hK.1⟩
  choose Kc hKcj hKc using hK
  let k : ℕ → ℕ := fun j => (Finset.range (j + 1)).sup Kc
  have hKk : ∀ j, Kc j ≤ k j := fun j => Finset.le_sup (Finset.self_mem_range_succ j)
  have hkmono : Monotone k := fun i j hij =>
    Finset.sup_mono (Finset.range_subset_range.2 (by omega))
  have hk : Tendsto k atTop atTop := tendsto_atTop_mono (fun j => (hKcj j).trans (hKk j)) tendsto_id
  let E : ℕ → Set (ContinuousPath ℂ) := fun j => clockCauchyEvent a (k j) (k (j + 1)) j
    ((1 / 2 : ℝ) ^ j)
  have hEm : ∀ j, MeasurableSet (E j) := fun j => measurableSet_clockCauchyEvent ha _ _ _ _
  have hEle : ∀ j, (Q ∘ₘ ρ) (E j) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
    intro j
    rw [Measure.bind_apply (hEm j) Q.measurable.aemeasurable]
    refine le_trans (lintegral_mono fun w => ?_) (hKc j)
    have h1 : Kc j + (k j - Kc j) = k j := Nat.add_sub_cancel' (hKk j)
    have h2 : Kc j + (k (j + 1) - Kc j) = k (j + 1) :=
      Nat.add_sub_cancel' ((hKk j).trans (hkmono (Nat.le_succ j)))
    refine le_trans ?_ (le_iSup (fun k' => ⨆ m : ℕ, Q w (clockCauchyEvent a (Kc j + k')
      (Kc j + m) j ((1 / 2 : ℝ) ^ j))) (k j - Kc j))
    refine le_trans ?_ (le_iSup (fun m => Q w (clockCauchyEvent a (Kc j + (k j - Kc j))
      (Kc j + m) j ((1 / 2 : ℝ) ^ j))) (k (j + 1) - Kc j))
    rw [h1, h2]
  have hsum : (∑' j, (Q ∘ₘ ρ) (E j)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hEle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  -- the good set of paths along which the subsequence is Cauchy
  let C : Set (ContinuousPath ℂ) := ⋃ N : ℕ, ⋂ j : ℕ, (E (N + j))ᶜ
  have hCm : MeasurableSet C := MeasurableSet.iUnion fun N => MeasurableSet.iInter fun j =>
    (hEm _).compl
  have hCref : ∀ᵐ w ∂ρ, ∀ᵐ b ∂(Q w), b ∈ C := by
    have hC : ∀ᵐ b ∂(Q ∘ₘ ρ), b ∈ C := by
      filter_upwards [ae_eventually_notMem hsum] with b hb
      obtain ⟨N, hN⟩ := eventually_atTop.1 hb
      exact mem_iUnion.2 ⟨N, mem_iInter.2 fun j => hN (N + j) (Nat.le_add_right N j)⟩
    exact Measure.ae_ae_of_ae_comp hC
  have hCauchy : ∀ b ∈ C, ∀ t : ℝ≥0, ∃ L, Tendsto (fun j => a (k j) b t) atTop (𝓝 L) := by
    intro b hb t
    obtain ⟨N, hN⟩ := mem_iUnion.1 hb
    obtain ⟨T₀, hT₀⟩ := exists_nat_ge t
    refine exists_tendsto_of_eventually_abs_sub_le (J := N + T₀) fun j hj => ?_
    by_contra hcon
    push Not at hcon
    have hjE : b ∉ E j := by
      have := mem_iInter.1 hN (j - N)
      rwa [Nat.add_sub_cancel' (by omega)] at this
    have hc : Continuous fun s => |a (k j) b s - a (k (j + 1)) b s| :=
      continuous_abs.comp ((ha.continuous _ b).sub (ha.continuous _ b))
    obtain ⟨q, hq0, hqT, hq⟩ := exists_rat_le_of_lt hc (T := (j : ℝ≥0))
      (hT₀.trans (by exact_mod_cast (show T₀ ≤ j by omega))) hcon
    exact hjE (mem_iUnion.2 ⟨q, hq0, by simpa using hqT, hq⟩)
  -- the clock
  let s : ℕ → ℝ≥0 := fun n => ((n : ℝ≥0) + 1)⁻¹
  have hs0 : ∀ n, 0 < s n := fun n => inv_pos.2 (by positivity)
  have hslim : Tendsto s atTop (𝓝 0) := by
    rw [← NNReal.tendsto_coe, NNReal.coe_zero]
    refine tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => ?_
    simp [s]
  have hsanti : Antitone s := fun m n hmn => by
    simp only [s]
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
  refine ⟨fun t b => (⨆ n : ℕ, limsup (fun j => ENNReal.ofReal
    (a (k j) b t - a (k j) b (min (s n) t))) atTop).toNNReal, fun t => ?_,
    fun m hm hmeas t => ?_, fun x hx r => ?_⟩
  · exact (Measurable.iSup fun n => Measurable.limsup fun j => ENNReal.measurable_ofReal.comp
      ((ha.measurable _ _).sub (ha.measurable _ _))).ennreal_toNNReal
  · have h1 : ∀ j n, Measurable[m t] fun b =>
        ENNReal.ofReal (a (k j) b t - a (k j) b (min (s n) t)) := fun j n =>
      ENNReal.measurable_ofReal.comp ((hmeas _ t).sub
        ((hmeas _ _).mono (hm (min_le_right _ _)) le_rfl))
    exact (Measurable.iSup fun n => Measurable.limsup fun j => h1 j n).ennreal_toNNReal
  obtain ⟨φ, hφ, hae⟩ := ae_tendsto_of_tendstoClockInMeasure ha (hF x hx) hk
  have hshift : ∀ᵐ b ∂(Q x), ∀ n, ContinuousPath.shift (r + s n) b ∈ C :=
    ae_all_iff.2 fun n => htr x hx (r + s n) (lt_of_lt_of_le (hs0 n) le_add_self) C hCm hCref
  filter_upwards [hae, hshift] with b ⟨hpt, h0, hcont, hmono⟩ hb u
  have hrw : ∀ j v, a (k j) (ContinuousPath.shift r b) v = a (k j) b (r + v) - a (k j) b r :=
    fun j v => by rw [ha.shift]; ring
  -- the increments converge, to `F x (r + u) - F x (r + s n ∧ u)`
  have hinc : ∀ n, Tendsto (fun j => a (k j) (ContinuousPath.shift r b) u -
      a (k j) (ContinuousPath.shift r b) (min (s n) u)) atTop
      (𝓝 (F x b (r + u) - F x b (r + min (s n) u))) := by
    intro n
    obtain ⟨L, hL⟩ : ∃ L, Tendsto (fun j => a (k j) (ContinuousPath.shift r b) u -
        a (k j) (ContinuousPath.shift r b) (min (s n) u)) atTop (𝓝 L) := by
      rcases le_total u (s n) with hus | hsu
      · refine ⟨0, ?_⟩
        simp only [min_eq_right hus, sub_self]
        exact tendsto_const_nhds
      · obtain ⟨L, hL⟩ := hCauchy _ (hb n) (u - s n)
        refine ⟨L, hL.congr fun j => ?_⟩
        rw [min_eq_left hsu, ← ContinuousPath.shift_add]
        conv_rhs => rw [← add_tsub_cancel_of_le hsu]
        rw [ha.shift]
        ring
    have hsub : Tendsto (fun i => a (k (φ i)) (ContinuousPath.shift r b) u -
        a (k (φ i)) (ContinuousPath.shift r b) (min (s n) u)) atTop
        (𝓝 (F x b (r + u) - F x b (r + min (s n) u))) := by
      simp only [hrw]
      have := ((hpt (r + u)).sub (hpt r)).sub ((hpt (r + min (s n) u)).sub (hpt r))
      rw [show F x b (r + u) - F x b (r + min (s n) u) =
        F x b (r + u) - F x b r - (F x b (r + min (s n) u) - F x b r) by ring]
      exact this
    rwa [tendsto_nhds_unique (hL.comp hφ) hsub] at hL
  have hFr : 0 ≤ F x b (r + u) - F x b r := sub_nonneg.2 (hmono le_self_add)
  have hlim : ∀ n, limsup (fun j => ENNReal.ofReal (a (k j) (ContinuousPath.shift r b) u -
      a (k j) (ContinuousPath.shift r b) (min (s n) u))) atTop =
      ENNReal.ofReal (F x b (r + u) - F x b (r + min (s n) u)) := fun n =>
    ((ENNReal.continuous_ofReal.tendsto _).comp (hinc n)).limsup_eq
  have hsup : (⨆ n : ℕ, ENNReal.ofReal (F x b (r + u) - F x b (r + min (s n) u))) =
      ENNReal.ofReal (F x b (r + u) - F x b r) := by
    refine iSup_eq_of_tendsto (fun m n hmn => ENNReal.ofReal_le_ofReal ?_) ?_
    · exact sub_le_sub_left (hmono (add_le_add_right (min_le_min_right u (hsanti hmn)) r)) _
    · have h0u : min (0 : ℝ≥0) u = 0 := min_eq_left (zero_le : (0 : ℝ≥0) ≤ u)
      have hm : Tendsto (fun n => r + min (s n) u) atTop (𝓝 r) := by
        have := (tendsto_const_nhds (x := r)).add (hslim.min (tendsto_const_nhds (x := u)))
        rwa [h0u, add_zero] at this
      have := (hcont.tendsto r).comp hm
      have h3 := (ENNReal.continuous_ofReal.tendsto _).comp
        ((tendsto_const_nhds (x := F x b (r + u))).sub this)
      simpa [Function.comp_def] using h3
  simp only [hlim, hsup]
  rw [ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal hFr]

/-- The universal clock agrees with the clock from every good start at all times. -/
theorem IsApproxClocks.ae_eq_of_shift_zero {μ : Measure (ContinuousPath ℂ)}
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {G : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (h : ∀ᵐ b ∂μ, ∀ u, (A u (ContinuousPath.shift 0 b) : ℝ) = G b (0 + u) - G b 0)
    (h0 : ∀ᵐ b ∂μ, G b 0 = 0) : ∀ᵐ b ∂μ, ∀ u, (A u b : ℝ) = G b u := by
  filter_upwards [h, h0] with b hb hb0 u
  have := hb u
  rwa [ContinuousPath.shift_zero, zero_add, hb0, sub_zero] at this

end HarmonicBalls
