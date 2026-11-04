import HarmonicBalls.Proofs.Sec6.BrownianAvoidance

/-! # Exit from shrinking balls

Planar Brownian motion leaves shrinking balls about its starting point at
arbitrarily small times. This uses the non-atomic one-time Gaussian marginals.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess ProbabilityTheory
open scoped ENNReal Topology

/-- At a positive time planar Brownian motion is almost surely not at its
starting point. -/
theorem ae_planarBrownianMotion_eval_ne (x : ℂ) (t : NNReal) (ht : t ≠ 0) :
    ∀ᵐ ω ∂(planarBrownianMotion x), ω t ≠ x := by
  have hreal : ∀ᵐ ω ∂(brownianMotion x.re), ω t ≠ x.re := by
    apply ae_iff.mpr
    have hz : gaussianReal x.re t {x.re} = 0 :=
      gaussianReal_absolutelyContinuous x.re ht (by simp)
    rw [← brownianMotion_map_eval t x.re,
      Measure.map_apply (show Measurable (fun ω : ContinuousPath ℝ => ω t) from
        ContinuousPath.measurable_coordinateProcess t)
        (measurableSet_singleton _)] at hz
    change (brownianMotion x.re) {ω | ω t = x.re} = 0 at hz
    simpa only [not_not] using hz
  have hproj : Measurable (fun ω : ContinuousPath ℂ => (reImPath ω).1) :=
    measurable_fst.comp measurable_reImPath
  have hset : MeasurableSet {p : ContinuousPath ℝ | p t ≠ x.re} :=
    (measurableSet_eq_fun (ContinuousPath.measurable_coordinateProcess t) measurable_const).compl
  have hmapae : ∀ᵐ p ∂((planarBrownianMotion x).map
      (fun ω => (reImPath ω).1)), p t ≠ x.re := by
    rw [planarBrownianMotion_map_re]
    exact hreal
  have hae := (ae_map_iff hproj.aemeasurable hset).mp hmapae
  filter_upwards [hae] with ω hω hEq
  apply hω
  simpa using congrArg Complex.re hEq

/-- A path which moves away from its initial point at arbitrarily small
positive times exits every sequence of shrinking balls at times tending to zero. -/
theorem tendsto_exitTime_ball_zero_of_eval_ne (ω : ContinuousPath ℂ) (x : ℂ)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    (hω : ∀ k : ℕ, ω ((1 / 2 : NNReal) ^ k) ≠ x) :
    Tendsto (fun n => ContinuousPath.exitTime (Metric.ball x (r n)) ω) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact (not_lt_of_ge bot_le ha).elim
  · intro b hb
    have hpow : Tendsto (fun k : ℕ => ((1 / 2 : ℝ≥0∞) ^ k)) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
    obtain ⟨k, hk⟩ := (eventually_atTop.mp (hpow.eventually (eventually_lt_nhds hb)))
    have hdist : 0 < dist (ω ((1 / 2 : NNReal) ^ k)) x := dist_pos.mpr (hω k)
    filter_upwards [hr.eventually (eventually_lt_nhds hdist)] with n hn
    have hexit := ContinuousPath.exitTime_le_of_notMem (Metric.ball x (r n)) ω
      ((1 / 2 : NNReal) ^ k) (by simpa only [Metric.mem_ball, not_lt] using hn.le)
    apply lt_of_le_of_lt hexit
    have hcoe : ((1 / 2 : NNReal) : ℝ≥0∞) = 1 / 2 := by norm_num
    simpa only [ENNReal.coe_pow, hcoe] using hk k le_rfl

/-- Exit times of balls centred at the starting point converge to zero when
the radii converge to zero. -/
theorem ae_tendsto_exitTime_ball_zero (x : ℂ) {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) :
    ∀ᵐ ω ∂(planarBrownianMotion x),
      Tendsto (fun n => ContinuousPath.exitTime (Metric.ball x (r n)) ω) atTop (𝓝 0) := by
  have h : ∀ᵐ ω ∂(planarBrownianMotion x),
      ∀ k : ℕ, ω ((1 / 2 : NNReal) ^ k) ≠ x := by
    rw [ae_all_iff]
    intro k
    exact ae_planarBrownianMotion_eval_ne x _ (pow_ne_zero _ (by norm_num))
  filter_upwards [h] with ω hω
  exact tendsto_exitTime_ball_zero_of_eval_ne ω x hr hω

/-- Lower bounds along arbitrarily small balls give the same lower bound for
instantaneous occurrence of a measurable nonnegative random time. -/
theorem le_probability_eq_zero_of_frequently_le_exitTime
    (x : ℂ) (τ : ContinuousPath ℂ → ℝ≥0∞) (hτ : Measurable τ)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) (hranti : Antitone r)
    (p : ℝ≥0∞)
    (hbound : ∃ᶠ n in atTop, p ≤ planarBrownianMotion x
      {ω | τ ω ≤ ContinuousPath.exitTime (Metric.ball x (r n)) ω}) :
    p ≤ planarBrownianMotion x {ω | τ ω = 0} := by
  let A : ℕ → Set (ContinuousPath ℂ) := fun n =>
    {ω | τ ω ≤ ContinuousPath.exitTime (Metric.ball x (r n)) ω}
  have hmeas : ∀ n, MeasurableSet (A n) := by
    intro n
    exact measurableSet_le hτ (ContinuousPath.measurable_exitTime _ Metric.isOpen_ball)
  have hanti : Antitone A := by
    intro m n hmn ω hω
    exact hω.trans (ContinuousPath.exitTime_mono
      (Metric.ball_subset_ball (hranti hmn)) ω)
  have hconv : Tendsto (fun n => planarBrownianMotion x (A n)) atTop
      (𝓝 (planarBrownianMotion x (⋂ n, A n))) := by
    exact tendsto_measure_iInter_atTop (fun n => (hmeas n).nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
  have hle : planarBrownianMotion x (⋂ n, A n) ≤
      planarBrownianMotion x {ω | τ ω = 0} := by
    apply measure_mono_ae
    filter_upwards [ae_tendsto_exitTime_ball_zero x hr] with ω hω hmem
    have hτle : τ ω ≤ 0 := ge_of_tendsto hω (Eventually.of_forall fun n =>
      (mem_iInter.mp hmem n))
    exact le_antisymm hτle bot_le
  exact (ge_of_tendsto_of_frequently hconv hbound).trans hle

/-- The first entry time into a countable union of compact sets is measurable. -/
theorem measurable_exitTime_compl_iUnion_compact (K : ℕ → Set ℂ)
    (hK : ∀ n, IsCompact (K n)) :
    Measurable (fun ω : ContinuousPath ℂ => ContinuousPath.exitTime (⋃ n, K n)ᶜ ω) := by
  simp_rw [exitTime_compl_iUnion]
  exact Measurable.iInf (fun n =>
    ContinuousPath.measurable_exitTime (K n)ᶜ (hK n).isClosed.isOpen_compl)

/-- Recurring lower bounds on hitting compact unions before exit imply the
same lower bound for hitting the union at time zero. -/
theorem le_instant_hit_probability_of_frequently_le_exitTime
    (x : ℂ) (K : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n))
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) (hranti : Antitone r)
    (p : ℝ≥0∞)
    (hbound : ∃ᶠ n in atTop, p ≤ planarBrownianMotion x
      {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω ≤
        ContinuousPath.exitTime (Metric.ball x (r n)) ω}) :
    p ≤ planarBrownianMotion x {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω = 0} :=
  le_probability_eq_zero_of_frequently_le_exitTime x _
    (measurable_exitTime_compl_iUnion_compact K hK) hr hranti p hbound

end HarmonicBalls.Section6
