import HarmonicBalls.Proofs.Potential.LQGClockInsertedExistence
import HarmonicBalls.Proofs.Potential.LQGClockExpectedExitFinite

/-! # Time-change properties of LQG clocks

An LQG clock is the limit in probability, uniformly on compact time intervals, of the clock
approximations, which are continuous, nondecreasing and vanish at time zero. Along a subsequence
the convergence is almost surely locally uniform, so almost every path has a clock that vanishes
at time zero, is continuous and is nondecreasing. Strict monotonicity then follows from strict
increase over every pair of rational times, and the clock is a time-change clock as soon as it
also tends to infinity. For a family of LQG clocks of the inserted field from every start, these
two properties give, for almost every field, finite expected exit times of Liouville Brownian
motion from every smooth bounded domain and every start in it.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- Clock approximations with a continuous field are continuous in time. -/
theorem continuous_lqgClockApprox {γ : ℝ} {hε : ℝ → ℂ → ℝ} {ε : ℝ} (hc : Continuous (hε ε))
    (b : ContinuousPath ℂ) : Continuous (lqgClockApprox γ hε ε b) := by
  have hg : Continuous (fun s : ℝ => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b s.toNNReal))) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (hc.comp (b.continuous.comp continuous_real_toNNReal))))
  exact (intervalIntegral.continuous_primitive (fun u v => hg.intervalIntegrable u v) 0).comp
    NNReal.continuous_coe

/-- Clock approximations at a positive scale are nondecreasing in time. -/
theorem monotone_lqgClockApprox {γ : ℝ} {hε : ℝ → ℂ → ℝ} {ε : ℝ} (hε0 : 0 < ε)
    (hc : Continuous (hε ε)) (b : ContinuousPath ℂ) : Monotone (lqgClockApprox γ hε ε b) := by
  intro s t hst
  have hg : Continuous (fun u : ℝ => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b u.toNNReal))) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (hc.comp (b.continuous.comp continuous_real_toNNReal))))
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  show (∫ u in (0 : ℝ)..(s : ℝ), ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b u.toNNReal))) ≤
    ∫ u in (0 : ℝ)..(t : ℝ), ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b u.toNNReal))
  rw [← sub_nonneg, intervalIntegral.integral_interval_sub_left (hg.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _)]
  exact intervalIntegral.integral_nonneg hst' fun u _ =>
    mul_nonneg (Real.rpow_nonneg hε0.le _) (Real.exp_pos _).le

/-- Almost every path has an LQG clock that vanishes at time zero, is continuous and is
nondecreasing. -/
theorem ae_zero_continuous_monotone_of_isLQGClock {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hcont : ∀ k : ℕ, Continuous (hε (dyadicScale k)))
    (hclock : IsLQGClock planarBrownianMotion γ hε x F) :
    ∀ᵐ b ∂(planarBrownianMotion x), F b 0 = 0 ∧ Continuous (F b) ∧ Monotone (F b) := by
  let μ := planarBrownianMotion x
  let A : ℕ → ContinuousPath ℂ → ℝ≥0 → ℝ := fun k => lqgClockApprox γ hε (dyadicScale k)
  let S : ℕ → ℕ → Set (ContinuousPath ℂ) := fun j k =>
    {b | ∃ t ≤ (j : ℝ≥0), 1 / ((j : ℝ) + 1) ≤ |A k b t - F b t|}
  have hsmall (j : ℕ) : ∃ k, μ (S j k) < ENNReal.ofReal ((1/2 : ℝ) ^ j) := by
    have h := hclock (j : ℝ≥0) (1 / ((j : ℝ) + 1)) (by positivity)
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ((1/2 : ℝ) ^ j) := ENNReal.ofReal_pos.mpr (by positivity)
    exact (h.eventually (gt_mem_nhds hpos)).exists
  choose kk hkk using hsmall
  have hsum : (∑' j, μ (S j (kk j))) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun j => (hkk j).le)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with b hb
  have hclose : ∀ᶠ j : ℕ in atTop, ∀ t : ℝ≥0, t ≤ (j : ℝ≥0) →
      |A (kk j) b t - F b t| < 1 / ((j : ℝ) + 1) := by
    filter_upwards [hb] with j hj t ht
    by_contra h
    exact hj ⟨t, ht, not_lt.mp h⟩
  have hsmallj : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hunif (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ j : ℕ in atTop, ∀ t : ℝ≥0, t ≤ T → |A (kk j) b t - F b t| < ε := by
    obtain ⟨N, hN⟩ := exists_nat_ge T
    filter_upwards [hclose, hsmallj.eventually (gt_mem_nhds hε),
      eventually_ge_atTop N] with j hj hjε hjN t ht
    exact (hj t (ht.trans (hN.trans (by exact_mod_cast hjN)))).trans hjε
  have hpt (t : ℝ≥0) : Tendsto (fun j => A (kk j) b t) atTop (𝓝 (F b t)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := (hunif t ε hε).exists_forall_of_atTop
    exact ⟨N, fun j hj => by rw [Real.dist_eq]; exact hN j hj t le_rfl⟩
  have hA0 (k : ℕ) : A k b 0 = 0 := by
    simp [A, lqgClockApprox]
  refine ⟨?_, ?_, ?_⟩
  · have h := hpt 0
    simp only [hA0] at h
    exact (tendsto_nhds_unique h tendsto_const_nhds)
  · have hloc : TendstoLocallyUniformly (fun j => A (kk j) b) (F b) atTop := by
      rw [tendstoLocallyUniformly_iff_forall_isCompact]
      intro K hK
      obtain ⟨T, hT⟩ := hK.bddAbove
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [hunif T ε hε] with j hj t ht
      rw [Real.dist_eq, abs_sub_comm]
      exact hj t (hT ht)
    exact hloc.continuous (Filter.Eventually.frequently (Filter.Eventually.of_forall fun j =>
      continuous_lqgClockApprox (hcont (kk j)) b))
  · intro s t hst
    exact le_of_tendsto_of_tendsto' (hpt s) (hpt t) fun j =>
      monotone_lqgClockApprox (dyadicScale_pos (kk j)) (hcont (kk j)) b hst

/-- An LQG clock is almost surely a time-change clock as soon as it almost surely increases
strictly between any two rational times and tends to infinity. -/
theorem ae_isTimeChangeClock_of_isLQGClock {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hcont : ∀ k : ℕ, Continuous (hε (dyadicScale k)))
    (hclock : IsLQGClock planarBrownianMotion γ hε x F)
    (hpos : ∀ s t : ℚ, 0 ≤ s → s < t → ∀ᵐ b ∂(planarBrownianMotion x),
      F b (s : ℝ).toNNReal < F b (t : ℝ).toNNReal)
    (hdiv : ∀ᵐ b ∂(planarBrownianMotion x), Tendsto (F b) atTop atTop) :
    ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F b) := by
  have hpos' : ∀ᵐ b ∂(planarBrownianMotion x), ∀ s t : ℚ, 0 ≤ s → s < t →
      F b (s : ℝ).toNNReal < F b (t : ℝ).toNNReal := by
    rw [ae_all_iff]
    intro s
    rw [ae_all_iff]
    intro t
    by_cases hs : 0 ≤ s
    · by_cases hst : s < t
      · filter_upwards [hpos s t hs hst] with b hb _ _
        exact hb
      · exact Filter.Eventually.of_forall fun b _ h => absurd h hst
    · exact Filter.Eventually.of_forall fun b h => absurd h hs
  filter_upwards [ae_zero_continuous_monotone_of_isLQGClock hcont hclock, hpos', hdiv]
    with b hb hbp hbd
  obtain ⟨h0, hc, hm⟩ := hb
  refine ⟨h0, hc, ?_, hbd⟩
  intro s t hst
  have hst' : (s : ℝ) < t := by exact_mod_cast hst
  obtain ⟨p, hsp, hpt⟩ := exists_rat_btwn hst'
  obtain ⟨q, hpq, hqt⟩ := exists_rat_btwn hpt
  have hp0 : (0 : ℝ) ≤ p := le_trans s.coe_nonneg hsp.le
  have hp0' : (0 : ℚ) ≤ p := by exact_mod_cast hp0
  have hpq' : p < q := by exact_mod_cast hpq
  have h1 : F b s ≤ F b (p : ℝ).toNNReal := by
    apply hm
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hp0]
    exact hsp.le
  have h3 : F b (q : ℝ).toNNReal ≤ F b t := by
    apply hm
    have hq0 : (0 : ℝ) ≤ q := hp0.trans hpq.le
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
    exact hqt.le
  exact lt_of_le_of_lt h1 (lt_of_lt_of_le (hbp p q hp0' hpq') h3)

/-- The LQG clock of the inserted field exists, and for almost every field it almost surely
vanishes at time zero, is continuous and is nondecreasing. -/
theorem exists_ae_isLQGClock_fieldCircleAverage_zero_continuous_monotone
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ} (hγ : 0 < γ)
    (hγ2 : γ ^ 2 < 2) (hα : α < lqgQ γ) :
    ∃ F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ, ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) x (F ω) ∧
      ∀ᵐ b ∂(planarBrownianMotion x), F ω b 0 = 0 ∧ Continuous (F ω b) ∧ Monotone (F ω b) := by
  obtain ⟨F, hF⟩ := exists_ae_isLQGClock_fieldCircleAverage hh x hγ hγ2 hα
  refine ⟨F, ?_⟩
  filter_upwards [hF, ae_continuous_fieldCircleAverage hh α] with ω hω hc
  exact ⟨hω, ae_zero_continuous_monotone_of_isLQGClock (fun k => hc _ (dyadicScale_pos k)) hω⟩


/-- For almost every field, the expected exit time of Liouville Brownian motion from every smooth
bounded domain is finite from every start in it, for every family of LQG clocks of the inserted
field from every start that almost surely increase strictly between rational times and tend to
infinity. -/
theorem ae_forall_expectedLBMExitTime_lt_top_of_strictly_increasing
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < lqgQ γ) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ
      (fieldCircleAverage α (hcirc ω)) x (F ω x))
    (hpos : ∀ᵐ ω ∂P, ∀ x : ℂ, ∀ s t : ℚ, 0 ≤ s → s < t → ∀ᵐ b ∂(planarBrownianMotion x),
      F ω x b (s : ℝ).toNNReal < F ω x b (t : ℝ).toNNReal)
    (hdiv : ∀ᵐ ω ∂P, ∀ x : ℂ, ∀ᵐ b ∂(planarBrownianMotion x), Tendsto (F ω x b) atTop atTop) :
    ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O → ∀ x ∈ O,
      expectedLBMExitTime (F ω x) O x < ⊤ := by
  have hlp : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc :=
    (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  have hT : ∀ᵐ ω ∂P, ∀ x : ℂ, ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F ω x b) := by
    filter_upwards [hF, hpos, hdiv, ae_continuous_fieldCircleAverage hlp α] with ω hω hp hd hc x
    exact ae_isTimeChangeClock_of_isLQGClock (fun k => hc _ (dyadicScale_pos k)) (hω x) (hp x)
      (hd x)
  exact ae_forall_expectedLBMExitTime_lt_top hh hγ hγ2 hα hμ F hF hT

end HarmonicBalls
