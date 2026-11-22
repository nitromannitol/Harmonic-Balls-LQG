import HarmonicBalls.Proofs.Potential.LQGClockOriginDivergenceLaw
import HarmonicBalls.Proofs.Brownian.PlanarBrownianMotion
import HarmonicBalls.Proofs.Brownian.PlanarHeatFeller

/-! # LQG clocks from every start from the positivity at one start

Positive occupation clocks from every Brownian starting point, by a transfer of future events
under the Markov property at a fixed time. For the dyadic scales `ε = 2^{-k}` let
`I^k_{a,b}(w) = ∫_a^b ε^{γ²/2} e^{γ h_ε(w_v)} dv` (`dyadicIncrementApprox`) and let `G_{a,b}` be its
lower limit in `[0, ∞]` (`dyadicIncrementLiminf`), a raw functional of the path chosen before any
clock.

* For every LQG clock `F` from a start `x` and `s ≤ a ≤ b ≤ t`, almost surely
  `G_{a,b} ≤ F(t) - F(s)`: along a subsequence the approximants converge almost surely, the
  integrand is nonnegative, and the lower limit along a subsequence dominates the lower limit.
* For `a > 0`, the laws of the path after time `a` started from any two points are equivalent: by
  the Markov property at time `a` both are mixtures of the Brownian laws over the planar Gaussian
  transition laws at time `a`, which are equivalent to each other. So an event of the future after
  time `a` of full probability from the origin has full probability from every start.
* If for almost every field `G_{a,b} > 0` almost surely from the origin for all rationals
  `0 < a < b`, then for almost every field, from every start, the clocks increase strictly
  between any two rational times.
* The clock from the origin then tends to infinity (Bertacco-Gwynne, Theorem 5.12 (B4), proved in
  `ae_ae_isTimeChangeClock_lqgClock_origin`). Along subsequences chosen from the origin, the lower
  limits of the approximants over `[1, N + 1]` are therefore unbounded in `N` almost surely from the
  origin; this is an event of the future after time `1`, so it has full probability from every
  start, and it bounds the clock from below. Hence the clocks from every start tend to infinity,
  they are time-change clocks, and the expected exit times of Liouville Brownian motion are finite
  from every start.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- The dyadic approximant `∫_a^b ε^{γ²/2} e^{γ h_ε(w_v)} dv` of the clock increment over `[a, b]`
at the scale `ε = 2^{-k}`. -/
noncomputable def dyadicIncrementApprox (γ : ℝ) (hε : ℝ → ℂ → ℝ) (k : ℕ) (a b : ℝ)
    (w : ContinuousPath ℂ) : ℝ :=
  ∫ v in a..b, dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) (w v.toNNReal))

/-- The lower limit in `[0, ∞]` of the dyadic approximants of the clock increment over `[a, b]`. -/
noncomputable def dyadicIncrementLiminf (γ : ℝ) (hε : ℝ → ℂ → ℝ) (a b : ℝ)
    (w : ContinuousPath ℂ) : ℝ≥0∞ :=
  liminf (fun k => ENNReal.ofReal (dyadicIncrementApprox γ hε k a b w)) atTop

theorem continuous_dyadicIncrementIntegrand {γ : ℝ} {hε : ℝ → ℂ → ℝ} {k : ℕ}
    (hc : Continuous (hε (dyadicScale k))) (w : ContinuousPath ℂ) :
    Continuous fun v : ℝ =>
      dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) (w v.toNNReal)) :=
  continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
    (hc.comp (w.continuous.comp continuous_real_toNNReal))))

theorem dyadicIncrementIntegrand_nonneg (γ : ℝ) (hε : ℝ → ℂ → ℝ) (k : ℕ) (w : ContinuousPath ℂ)
    (v : ℝ) : 0 ≤ dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) (w v.toNNReal)) :=
  mul_nonneg (Real.rpow_nonneg (dyadicScale_pos k).le _) (Real.exp_pos _).le

/-- The increment of the approximating clock is the dyadic approximant of the increment. -/
theorem lqgClockApprox_sub_eq_dyadicIncrementApprox {γ : ℝ} {hε : ℝ → ℂ → ℝ} {k : ℕ}
    (hc : Continuous (hε (dyadicScale k))) (w : ContinuousPath ℂ) (s t : ℝ≥0) :
    lqgClockApprox γ hε (dyadicScale k) w t - lqgClockApprox γ hε (dyadicScale k) w s =
      dyadicIncrementApprox γ hε k s t w :=
  intervalIntegral.integral_interval_sub_left
    ((continuous_dyadicIncrementIntegrand hc w).intervalIntegrable _ _)
    ((continuous_dyadicIncrementIntegrand hc w).intervalIntegrable _ _)

/-- The dyadic approximants are monotone in the interval. -/
theorem dyadicIncrementApprox_mono {γ : ℝ} {hε : ℝ → ℂ → ℝ} {k : ℕ}
    (hc : Continuous (hε (dyadicScale k))) (w : ContinuousPath ℂ) {s a b t : ℝ} (hsa : s ≤ a)
    (hab : a ≤ b) (hbt : b ≤ t) :
    dyadicIncrementApprox γ hε k a b w ≤ dyadicIncrementApprox γ hε k s t w :=
  intervalIntegral.integral_mono_interval hsa hab hbt
    (Eventually.of_forall fun v => dyadicIncrementIntegrand_nonneg γ hε k w v)
    ((continuous_dyadicIncrementIntegrand hc w).intervalIntegrable _ _)

/-- The dyadic approximant over `[a, b]` is the approximant over `[0, b - a]` of the path shifted
by `a`. -/
theorem dyadicIncrementApprox_shift (γ : ℝ) (hε : ℝ → ℂ → ℝ) (k : ℕ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (w : ContinuousPath ℂ) :
    dyadicIncrementApprox γ hε k a b w =
      dyadicIncrementApprox γ hε k 0 (b - a) (ContinuousPath.shift a.toNNReal w) := by
  let g : ℝ → ℝ := fun v =>
    dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) (w v.toNNReal))
  have h1 := intervalIntegral.integral_comp_add_left g a (a := 0) (b := b - a)
  rw [add_zero, add_sub_cancel] at h1
  show (∫ v in a..b, g v) = _
  rw [← h1]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le (sub_nonneg.mpr hab)] at hu
  simp only [g, ContinuousPath.shift_apply, Real.toNNReal_add ha hu.1]

theorem dyadicIncrementLiminf_shift (γ : ℝ) (hε : ℝ → ℂ → ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (w : ContinuousPath ℂ) :
    dyadicIncrementLiminf γ hε a b w =
      dyadicIncrementLiminf γ hε 0 (b - a) (ContinuousPath.shift a.toNNReal w) := by
  unfold dyadicIncrementLiminf
  congr 1
  funext k
  rw [dyadicIncrementApprox_shift γ hε k ha hab]

/-- The approximating clock at a fixed time is a measurable function of the path. -/
theorem measurable_lqgClockApprox_time {γ : ℝ} {hε : ℝ → ℂ → ℝ} {k : ℕ}
    (hc : Continuous (hε (dyadicScale k))) (t : ℝ≥0) :
    Measurable fun w : ContinuousPath ℂ => lqgClockApprox γ hε (dyadicScale k) w t := by
  obtain ⟨D, hDm, hD⟩ := exists_measurable_lqgClockApprox_decoder γ (dyadicScale_pos k).le t
  have h : (fun w => lqgClockApprox γ hε (dyadicScale k) w t) =
      fun w => D (hε (dyadicScale k), w) := funext fun w => (hD _ hc w).symm
  rw [h]
  exact hDm.comp (measurable_const.prodMk measurable_id)

theorem measurable_dyadicIncrementApprox_zero {γ : ℝ} {hε : ℝ → ℂ → ℝ} {k : ℕ}
    (hc : Continuous (hε (dyadicScale k))) {c : ℝ} (hc0 : 0 ≤ c) :
    Measurable (dyadicIncrementApprox γ hε k 0 c) := by
  have h : dyadicIncrementApprox γ hε k 0 c =
      fun w => lqgClockApprox γ hε (dyadicScale k) w c.toNNReal := by
    funext w
    simp only [dyadicIncrementApprox, lqgClockApprox, Real.coe_toNNReal _ hc0]
  rw [h]
  exact measurable_lqgClockApprox_time hc _

/-- The lower limit along a subsequence dominates the lower limit. -/
theorem liminf_le_liminf_comp_of_strictMono (u : ℕ → ℝ≥0∞) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    liminf u atTop ≤ liminf (u ∘ ψ) atTop := by
  simp only [liminf_eq_iSup_iInf_of_nat]
  refine iSup_mono fun n => le_iInf₂ fun j hj => ?_
  exact iInf₂_le (ψ j) (hj.trans (hψ.id_le j))

/-- The dyadic approximants of the increment of an LQG clock converge to the increment in
probability. -/
theorem tendstoInMeasure_dyadicIncrementApprox_of_isLQGClock {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hF : IsLQGClock planarBrownianMotion γ hε x F)
    (hc : ∀ k, Continuous (hε (dyadicScale k))) (s t : ℝ≥0) :
    TendstoInMeasure (planarBrownianMotion x) (fun k w => dyadicIncrementApprox γ hε k s t w)
      atTop (fun w => F w t - F w s) := by
  rw [tendstoInMeasure_iff_norm]
  intro η hη
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hF (max s t) (η / 2) (by positivity)) (fun k => zero_le) fun k => measure_mono ?_
  intro w hw
  simp only [mem_ofPred_eq, Real.norm_eq_abs] at hw
  rw [← lqgClockApprox_sub_eq_dyadicIncrementApprox (hc k)] at hw
  by_contra hcon
  simp only [mem_ofPred_eq, not_exists, not_and, not_le] at hcon
  have h1 := hcon t (le_max_right _ _)
  have h2 := hcon s (le_max_left _ _)
  have h3 : |lqgClockApprox γ hε (dyadicScale k) w t - lqgClockApprox γ hε (dyadicScale k) w s -
      (F w t - F w s)| ≤ |lqgClockApprox γ hε (dyadicScale k) w t - F w t| +
        |lqgClockApprox γ hε (dyadicScale k) w s - F w s| := by
    rw [show lqgClockApprox γ hε (dyadicScale k) w t - lqgClockApprox γ hε (dyadicScale k) w s -
        (F w t - F w s) = (lqgClockApprox γ hε (dyadicScale k) w t - F w t) -
          (lqgClockApprox γ hε (dyadicScale k) w s - F w s) by ring]
    exact abs_sub _ _
  linarith

/-- For an LQG clock, along every subsequence, the lower limit of the dyadic approximants of an
increment is almost surely at most the increment of the clock. -/
theorem ae_liminf_comp_le_of_isLQGClock {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hF : IsLQGClock planarBrownianMotion γ hε x F)
    (hc : ∀ k, Continuous (hε (dyadicScale k))) (s t : ℝ≥0) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∀ᵐ w ∂(planarBrownianMotion x),
      liminf (fun j => ENNReal.ofReal (dyadicIncrementApprox γ hε (φ j) s t w)) atTop ≤
        ENNReal.ofReal (F w t - F w s) := by
  have hconv : TendstoInMeasure (planarBrownianMotion x)
      (fun j w => dyadicIncrementApprox γ hε (φ j) s t w) atTop (fun w => F w t - F w s) :=
    fun ε hε => (tendstoInMeasure_dyadicIncrementApprox_of_isLQGClock hF hc s t ε hε).comp
      hφ.tendsto_atTop
  obtain ⟨ψ, hψ, hψae⟩ := hconv.exists_seq_tendsto_ae
  filter_upwards [hψae] with w hw
  calc liminf (fun j => ENNReal.ofReal (dyadicIncrementApprox γ hε (φ j) s t w)) atTop
      ≤ liminf ((fun j => ENNReal.ofReal (dyadicIncrementApprox γ hε (φ j) s t w)) ∘ ψ) atTop :=
        liminf_le_liminf_comp_of_strictMono _ hψ
    _ = ENNReal.ofReal (F w t - F w s) :=
        ((ENNReal.continuous_ofReal.tendsto _).comp hw).liminf_eq

/-- For an LQG clock and `s ≤ a ≤ b ≤ t`, almost surely
`G_{a,b} ≤ F(t) - F(s)`. -/
theorem ae_dyadicIncrementLiminf_le_of_isLQGClock {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hF : IsLQGClock planarBrownianMotion γ hε x F)
    (hc : ∀ k, Continuous (hε (dyadicScale k))) {s t : ℝ≥0} {a b : ℝ} (hsa : (s : ℝ) ≤ a)
    (hab : a ≤ b) (hbt : b ≤ t) :
    ∀ᵐ w ∂(planarBrownianMotion x), dyadicIncrementLiminf γ hε a b w ≤
      ENNReal.ofReal (F w t - F w s) := by
  filter_upwards [ae_liminf_comp_le_of_isLQGClock hF hc s t strictMono_id] with w hw
  refine le_trans (liminf_le_liminf (Eventually.of_forall fun k => ?_)) hw
  exact ENNReal.ofReal_le_ofReal (dyadicIncrementApprox_mono (hc k) w hsa hab hbt)

/-- For `a > 0`, the law of the planar Brownian path after time `a` from any start is absolutely
continuous with respect to its law from any other start: both are mixtures of Brownian laws over
the planar Gaussian transition laws at time `a`, which are equivalent. -/
theorem planarBrownianMotion_map_shift_absolutelyContinuous {a : ℝ≥0} (ha : 0 < a) (y z : ℂ) :
    (planarBrownianMotion y).map (ContinuousPath.shift a) ≪
      (planarBrownianMotion z).map (ContinuousPath.shift a) := by
  let K := SubMarkovKernelSemigroup.IsConservative.continuousProcess
    planarHeatSemigroup isConservative_planarHeatSemigroup
  have hs (x : ℂ) : (planarBrownianMotion x).map (ContinuousPath.shift a) =
      K ∘ₘ planarHeatSemigroup.kernel a x := by
    rw [planarBrownianMotion_eq_continuousProcess]
    have hshift := congrArg (fun K => K x)
      (SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_shift
        planarHeatSemigroup isConservative_planarHeatSemigroup
        isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup a)
    rw [Kernel.map_apply _ (ContinuousPath.measurable_shift_fixed a) x,
      Kernel.comp_apply] at hshift
    exact hshift
  rw [hs y, hs z]
  refine Measure.AbsolutelyContinuous.comp_right ?_ K
  show planarHeatKernel a y ≪ planarHeatKernel a z
  rw [planarHeatKernel_apply, planarHeatKernel_apply, planarGaussian, planarGaussian]
  have hre : gaussianReal y.re a ≪ gaussianReal z.re a :=
    (gaussianReal_absolutelyContinuous _ ha.ne').trans (gaussianReal_absolutelyContinuous' _ ha.ne')
  have him : gaussianReal y.im a ≪ gaussianReal z.im a :=
    (gaussianReal_absolutelyContinuous _ ha.ne').trans (gaussianReal_absolutelyContinuous' _ ha.ne')
  exact (hre.prod him).map Complex.measurableEquivRealProd.symm.measurable

/-- An event of the future after time `a > 0` that holds almost surely from one start holds almost
surely from every start. -/
theorem ae_shift_mem_of_ae_shift_mem {a : ℝ≥0} (ha : 0 < a) {E : Set (ContinuousPath ℂ)}
    (hE : MeasurableSet E) {z : ℂ}
    (h : ∀ᵐ w ∂(planarBrownianMotion z), ContinuousPath.shift a w ∈ E) (y : ℂ) :
    ∀ᵐ w ∂(planarBrownianMotion y), ContinuousPath.shift a w ∈ E := by
  have hm : Measurable (ContinuousPath.shift a : ContinuousPath ℂ → ContinuousPath ℂ) :=
    ContinuousPath.measurable_shift_fixed a
  have h' : ∀ᵐ w' ∂((planarBrownianMotion z).map (ContinuousPath.shift a)), w' ∈ E :=
    (ae_map_iff (p := fun w' => w' ∈ E) hm.aemeasurable hE).mpr h
  exact (ae_map_iff (p := fun w' => w' ∈ E) hm.aemeasurable hE).mp
    ((planarBrownianMotion_map_shift_absolutelyContinuous ha y z).ae_le h')

/-- Strict increase from every start: if for almost every field `G_{a,b} > 0` almost surely from
the origin for all rationals `0 < a < b`, then for almost every field, from every start, every LQG
clock of the inserted field increases strictly between any two rational times. -/
theorem ae_forall_rat_lt_of_dyadicIncrementLiminf_pos {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) x (F ω x))
    (hone : ∀ᵐ ω ∂P, ∀ a b : ℚ, 0 < a → a < b → ∀ᵐ w ∂(planarBrownianMotion 0),
      0 < dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) a b w) :
    ∀ᵐ ω ∂P, ∀ x : ℂ, ∀ s t : ℚ, 0 ≤ s → s < t → ∀ᵐ w ∂(planarBrownianMotion x),
      F ω x w (s : ℝ).toNNReal < F ω x w (t : ℝ).toNNReal := by
  filter_upwards [hF, hone, ae_continuous_fieldCircleAverage hh α] with ω hFω honeω hcω
  intro x s t hs hst
  have hc : ∀ k, Continuous (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k)) :=
    fun k => hcω _ (dyadicScale_pos k)
  set a : ℚ := s + (t - s) / 3 with hadef
  set b : ℚ := s + 2 * (t - s) / 3 with hbdef
  have hts : 0 < t - s := sub_pos.mpr hst
  have ha : 0 < a := by rw [hadef]; linarith
  have hab : a < b := by rw [hadef, hbdef]; linarith
  have hsa : s ≤ a := by rw [hadef]; linarith
  have hbt : b ≤ t := by rw [hbdef]; linarith
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab.le
  let E : Set (ContinuousPath ℂ) := {w' | 0 < dyadicIncrementLiminf γ
    (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) 0 ((b : ℝ) - a) w'}
  have hE : MeasurableSet E :=
    measurableSet_lt measurable_const (Measurable.liminf fun k =>
      (measurable_dyadicIncrementApprox_zero (hc k) (sub_nonneg.mpr hab')).ennreal_ofReal)
  have h0 : ∀ᵐ w ∂(planarBrownianMotion 0), ContinuousPath.shift (a : ℝ).toNNReal w ∈ E := by
    filter_upwards [honeω a b ha hab] with w hw
    show 0 < dyadicIncrementLiminf γ _ 0 ((b : ℝ) - a) _
    rwa [← dyadicIncrementLiminf_shift γ _ ha'.le hab']
  have hy := ae_shift_mem_of_ae_shift_mem (Real.toNNReal_pos.mpr ha') hE h0 x
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs
  have ht' : (0 : ℝ) ≤ t := by exact_mod_cast (hs.trans hst.le)
  have hsa' : (((s : ℝ).toNNReal : ℝ≥0) : ℝ) ≤ a := by
    rw [Real.coe_toNNReal _ hs']
    exact_mod_cast hsa
  have hbt' : (b : ℝ) ≤ (((t : ℝ).toNNReal : ℝ≥0) : ℝ) := by
    rw [Real.coe_toNNReal _ ht']
    exact_mod_cast hbt
  filter_upwards [hy, ae_dyadicIncrementLiminf_le_of_isLQGClock (hFω x) hc hsa' hab' hbt']
    with w hw1 hw2
  have hpos : 0 < dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω))
      a b w := by
    rw [dyadicIncrementLiminf_shift γ _ ha'.le hab']
    exact hw1
  have := ENNReal.ofReal_pos.mp (lt_of_lt_of_le hpos hw2)
  linarith

/-- Divergence of the clocks from every start from the divergence from the origin: along
subsequences chosen from the origin, the lower limits of the dyadic approximants over `[1, N + 1]`
are almost surely unbounded in `N` from the origin; this is an event of the future after time `1`,
hence it holds almost surely from every start, where these lower limits bound the clock from
below. -/
theorem ae_forall_tendsto_atTop_of_origin {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) x (F ω x))
    (hdiv0 : ∀ᵐ ω ∂P, ∀ᵐ w ∂(planarBrownianMotion 0), Tendsto (F ω 0 w) atTop atTop) :
    ∀ᵐ ω ∂P, ∀ x : ℂ, ∀ᵐ w ∂(planarBrownianMotion x), Tendsto (F ω x w) atTop atTop := by
  filter_upwards [hF, hdiv0, ae_continuous_fieldCircleAverage hh α] with ω hFω hdω hcω
  intro x
  set hε := LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) with hεdef
  have hc : ∀ k, Continuous (hε (dyadicScale k)) := fun k => hcω _ (dyadicScale_pos k)
  have hT1 (N : ℕ) : ((1 : ℝ≥0) : ℝ) ≤ (((N : ℝ≥0) + 1 : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast]
    linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hT1' (N : ℕ) : (((N : ℝ≥0) + 1 : ℝ≥0) : ℝ) - ((1 : ℝ≥0) : ℝ) = N := by
    simp only [NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast]
    ring
  choose φ hφ hφae using fun N : ℕ =>
    (tendstoInMeasure_dyadicIncrementApprox_of_isLQGClock (hFω 0) hc 1
      ((N : ℝ≥0) + 1)).exists_seq_tendsto_ae
  let L : ℕ → ContinuousPath ℂ → ℝ≥0∞ := fun N w' =>
    liminf (fun j => ENNReal.ofReal (dyadicIncrementApprox γ hε (φ N j) 0 N w')) atTop
  have hLm (N : ℕ) : Measurable (L N) :=
    Measurable.liminf fun j =>
      (measurable_dyadicIncrementApprox_zero (hc _) (Nat.cast_nonneg N)).ennreal_ofReal
  have hLshift (N : ℕ) (w : ContinuousPath ℂ) :
      L N (ContinuousPath.shift ((1 : ℝ≥0) : ℝ).toNNReal w) =
        liminf (fun j => ENNReal.ofReal (dyadicIncrementApprox γ hε (φ N j) (1 : ℝ≥0)
          (((N : ℝ≥0) + 1 : ℝ≥0) : ℝ) w))
          atTop := by
    simp only [L]
    congr 1
    funext j
    rw [dyadicIncrementApprox_shift γ hε _ (NNReal.coe_nonneg 1) (hT1 N), hT1']
  let E : Set (ContinuousPath ℂ) := {w' | ∀ M : ℕ, ∃ N : ℕ, (M : ℝ≥0∞) ≤ L N w'}
  have hE : MeasurableSet E := by
    have : E = ⋂ M : ℕ, ⋃ N : ℕ, {w' | (M : ℝ≥0∞) ≤ L N w'} := by
      ext w'
      simp [E]
    rw [this]
    exact MeasurableSet.iInter fun M => MeasurableSet.iUnion fun N =>
      measurableSet_le measurable_const (hLm N)
  have hone : (0 : ℝ≥0) < ((1 : ℝ≥0) : ℝ).toNNReal := by simp
  have h0 : ∀ᵐ w ∂(planarBrownianMotion 0),
      ContinuousPath.shift ((1 : ℝ≥0) : ℝ).toNNReal w ∈ E := by
    filter_upwards [ae_all_iff.mpr hφae, hdω] with w hconv hdiv
    intro M
    have hTt : Tendsto (fun N : ℕ => (N : ℝ≥0) + 1) atTop atTop :=
      tendsto_atTop_mono (fun N => le_add_of_nonneg_right zero_le_one)
        tendsto_natCast_atTop_atTop
    obtain ⟨N, hN⟩ := (hTt.eventually (hdiv.eventually_ge_atTop ((M : ℝ) + F ω 0 w 1))).exists
    refine ⟨N, ?_⟩
    have hlim : liminf (fun j => ENNReal.ofReal
        (dyadicIncrementApprox γ hε (φ N j) (1 : ℝ≥0) (((N : ℝ≥0) + 1 : ℝ≥0) : ℝ) w)) atTop =
          ENNReal.ofReal (F ω 0 w ((N : ℝ≥0) + 1) - F ω 0 w 1) :=
      ((ENNReal.continuous_ofReal.tendsto _).comp (hconv N)).liminf_eq
    rw [hLshift N w, hlim, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hy := ae_shift_mem_of_ae_shift_mem hone hE h0 x
  have hle : ∀ᵐ w ∂(planarBrownianMotion x), ∀ N : ℕ,
      L N (ContinuousPath.shift ((1 : ℝ≥0) : ℝ).toNNReal w) ≤
        ENNReal.ofReal (F ω x w ((N : ℝ≥0) + 1) - F ω x w 1) := by
    rw [ae_all_iff]
    intro N
    filter_upwards [ae_liminf_comp_le_of_isLQGClock (hFω x) hc 1 ((N : ℝ≥0) + 1) (hφ N)]
      with w hw
    rw [hLshift N w]
    exact hw
  filter_upwards [hy, hle, ae_zero_continuous_monotone_of_isLQGClock hc (hFω x)]
    with w hwE hwle hwm
  refine tendsto_atTop_atTop_of_monotone hwm.2.2 fun M => ?_
  obtain ⟨N, hN⟩ := hwE ⌈M - F ω x w 1⌉₊
  refine ⟨(N : ℝ≥0) + 1, ?_⟩
  have h1 : F ω x w 1 ≤ F ω x w ((N : ℝ≥0) + 1) :=
    hwm.2.2 (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have h2 := (hN.trans (hwle N))
  rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff (by linarith)] at h2
  have h3 := Nat.le_ceil (M - F ω x w 1)
  linarith

/-- The time-change property from every start: if for almost every field `G_{a,b} > 0` almost
surely from the origin for all rationals `0 < a < b`, then for almost every field, from every
start, every LQG clock of the inserted field (`0 < γ`, `γ² < 2`, `α < Q`) is almost surely a
time-change clock. -/
theorem ae_forall_isTimeChangeClock_of_dyadicIncrementLiminf_pos {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ)
    (hγ2 : γ ^ 2 < 2) (hα : α < lqgQ γ) (F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) x (F ω x))
    (hone : ∀ᵐ ω ∂P, ∀ a b : ℚ, 0 < a → a < b → ∀ᵐ w ∂(planarBrownianMotion 0),
      0 < dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) a b w) :
    ∀ᵐ ω ∂P, ∀ x : ℂ, ∀ᵐ w ∂(planarBrownianMotion x), IsTimeChangeClock (F ω x w) := by
  have hpos := ae_forall_rat_lt_of_dyadicIncrementLiminf_pos hh F hF hone
  have hF0 : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) 0 (F ω 0) := by
    filter_upwards [hF] with ω hω
    exact hω 0
  have hpos0 : ∀ᵐ ω ∂P, ∀ s t : ℚ, 0 ≤ s → s < t → ∀ᵐ w ∂(planarBrownianMotion (0 : ℂ)),
      F ω 0 w (s : ℝ).toNNReal < F ω 0 w (t : ℝ).toNNReal := by
    filter_upwards [hpos] with ω hω
    exact hω 0
  have hdiv0 : ∀ᵐ ω ∂P, ∀ᵐ w ∂(planarBrownianMotion 0), Tendsto (F ω 0 w) atTop atTop := by
    filter_upwards [ae_ae_isTimeChangeClock_lqgClock_origin hh hγ hγ2 hα (fun ω => F ω 0) hF0
      hpos0] with ω hω
    filter_upwards [hω] with w hw
    exact hw.tendsto_atTop
  filter_upwards [hF, hpos, ae_forall_tendsto_atTop_of_origin hh F hF hdiv0,
    ae_continuous_fieldCircleAverage hh α] with ω hFω hpω hdω hcω x
  exact ae_isTimeChangeClock_of_isLQGClock (fun k => hcω _ (dyadicScale_pos k)) (hFω x)
    (hpω x) (hdω x)

/-- Finite expected exit times of Liouville Brownian motion from every start from the positivity
at one start: for almost every field, from every smooth bounded domain and every start in it. -/
theorem ae_forall_expectedLBMExitTime_lt_top_of_dyadicIncrementLiminf_pos
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2)
    (hα : α < lqgQ γ) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ
      (fieldCircleAverage α (hcirc ω)) x (F ω x))
    (hone : ∀ᵐ ω ∂P, ∀ a b : ℚ, 0 < a → a < b → ∀ᵐ w ∂(planarBrownianMotion 0),
      0 < dyadicIncrementLiminf γ (fieldCircleAverage α (hcirc ω)) a b w) :
    ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O → ∀ x ∈ O,
      expectedLBMExitTime (F ω x) O x < ⊤ := by
  have hlp : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc :=
    (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  have hγ2' : γ < 2 := by nlinarith
  have hpos := ae_forall_rat_lt_of_dyadicIncrementLiminf_pos hlp F hF hone
  have hT := ae_forall_isTimeChangeClock_of_dyadicIncrementLiminf_pos hlp hγ hγ2 hα F hF hone
  have hdiv : ∀ᵐ ω ∂P, ∀ x : ℂ, ∀ᵐ w ∂(planarBrownianMotion x),
      Tendsto (F ω x w) atTop atTop := by
    filter_upwards [hT] with ω hω x
    filter_upwards [hω x] with w hw
    exact hw.tendsto_atTop
  exact ae_forall_expectedLBMExitTime_lt_top_of_strictly_increasing hh hγ hγ2' hα hμ F hF hpos
    hdiv

end HarmonicBalls
