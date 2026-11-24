import HarmonicBalls.Proofs.Potential.LQGSmoothGreenIntegralConvergence
import HarmonicBalls.Proofs.Potential.LQGSmoothGreenWeightedConvergence
import HarmonicBalls.Proofs.Potential.LQGClockExitWeightedSummability
import HarmonicBalls.Proofs.Potential.LQGClockExitWeightedLowerBound
import HarmonicBalls.Proofs.Potential.LQGClockExitDomainComparison
import HarmonicBalls.Proofs.Potential.LQGGreenPotentialHolderInput
import HarmonicBalls.Proofs.Potential.LQGClockExpectationLimit
import HarmonicBalls.Proofs.Potential.LQGActualLimitBallPower
import HarmonicBalls.Proofs.Sec6.FineSupportDisc
import HarmonicBalls.Proofs.Sec6.GreenIntegrability

/-!
# Expected exit times of Liouville Brownian motion: the Green identity and Hölder continuity

For `0 < γ < 2` and every insertion `α < Q`, for every family of LQG clocks from every start that
are almost surely time-change clocks, for almost every field, for every smooth bounded domain `O`
and every start `x ∈ O`, the expected exit time of Liouville Brownian motion from `O` is the Green
potential of the LQG measure,

  `E_x[τ_O] = ∫_O 2 G_O(x, y) μ_h(dy)`.

The Green clause of Proposition 2.5 then makes `x ↦ E_x[τ_O]` Hölder continuous on `O`.

The proof, on one field event:

* (upper bound) by Fatou's lemma `E_x[τ_O]` is at most the limit of the Green integrals of the
  approximating measures, which is `∫ 2 G_O(x, y) μ_h(dy)` for every smooth `O` and every pole
  (`IsWholePlaneGFF.ae_tendsto_green_lintegral_smooth`);
* (discs, away from the insertion) for the discs `D_n = B(0, n + 1)` and the weights
  `φ_m = greenPoleCutoff 0 2^{-m}`, which vanish on `B(0, 2^{-m})`, the exit-time increments of the
  weighted clock approximations have finite expected sum from Lebesgue almost every start, for
  every insertion (`ae_ae_lintegral_tsum_exit_weighted_increment_ne_top`); the Markov property
  at a fixed time and the continuity of the weighted Green potential give
  `E_x[τ_{D_n}] ≥ ∫ 2 G_{D_n}(x, y) φ_m(y) μ_h(dy)` from every start
  (`le_expectedLBMExitTime_of_ae_lintegral_tsum_ne_top_of_le`), and `m → ∞` removes the weight,
  since `μ_h` has no atom at the insertion point;
* (every domain) for `O ⊆ D_n`, `E_x[τ_{D_n}] ≤ E_x[τ_O] + (V_{D_n}(x) - V_O(x))`
  (`expectedLBMExitTime_le_add_sub_of_subset`), which with the identity for `D_n` gives the
  lower bound for `O`.

With the time-change property from every start supplied by the positivity of the clock increments
from the origin (`ae_forall_isTimeChangeClock_of_dyadicIncrementLiminf_pos`, `γ² < 2`), this is
the LBM clause of Proposition 2.5 (`GreenPotentialLiouvilleHolderStmt`) under the one-start
positivity event. That event is proved for `γ² < 2`
(`ae_forall_rat_ae_dyadicIncrementLiminf_pos`), and `greenPotentialLiouvilleHolder_lbmClause` is the
clause without it.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology Metric
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- The pole cutoff at the origin vanishes on the disc of its radius. -/
theorem greenPoleCutoff_zero_of_norm_lt {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ < r) :
    greenPoleCutoff 0 r z = 0 := by
  have h : ‖z‖ / r - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hr]
    exact hz.le
  simp only [greenPoleCutoff, dist_zero_right, max_eq_left h, min_eq_right zero_le_one]

/-- The pole cutoffs at the origin at the dyadic radii tend to one away from the origin. -/
theorem eventually_greenPoleCutoff_dyadicScale_eq_one {z : ℂ} (hz : z ≠ 0) :
    ∀ᶠ m in atTop, greenPoleCutoff 0 (dyadicScale m) z = 1 := by
  have ht : Tendsto (fun m : ℕ => 2 * dyadicScale m) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num)).const_mul 2
    rwa [mul_zero] at h
  filter_upwards [ht.eventually (gt_mem_nhds (norm_pos_iff.mpr hz))] with m hm
  exact greenPoleCutoff_eq_one (dyadicScale_pos m) (by rw [dist_zero_right]; exact hm.le)

/-- **Green identity for expected exit times of Liouville Brownian motion from every start, for
every insertion.** For `0 < γ < 2` and `α < Q`, for every family of LQG clocks from every start
that are almost surely time-change clocks, for almost every field, for every smooth bounded domain
`O` and every `x ∈ O`, `E_x[τ_O] = ∫_O G_O(x, y) 2 μ_h(dy)`. -/
theorem ae_forall_expectedLBMExitTime_eq_green
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < lqgQ γ) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ
      (fieldCircleAverage α (hcirc ω)) x (F ω x))
    (hT : ∀ᵐ ω ∂P, ∀ x : ℂ, ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F ω x b)) :
    ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O → ∀ x ∈ O,
      expectedLBMExitTime (F ω x) O x =
        ENNReal.ofReal (∫ y in O, greenFunction O x y * 2 ∂(μ ω)) := by
  have hlp : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc :=
    (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  let D : ℕ → Set ℂ := fun n => ball (0 : ℂ) ((n : ℝ) + 1)
  have hDs (n : ℕ) : IsSmoothBoundedOpen (D n) :=
    Section6.isSmoothBoundedOpen_disc 0 (by positivity)
  let φ : ℕ → ℂ → ℝ := fun m => greenPoleCutoff 0 (dyadicScale m)
  have hφc (m : ℕ) : Continuous (φ m) := by
    show Continuous (greenPoleCutoff 0 (dyadicScale m))
    unfold greenPoleCutoff
    fun_prop
  have hφ0 (m : ℕ) (z : ℂ) : 0 ≤ φ m z := (greenPoleCutoff_mem_Icc 0 _ z).1
  have hφ1 (m : ℕ) (z : ℂ) : φ m z ≤ 1 := (greenPoleCutoff_mem_Icc 0 _ z).2
  have hsum := ae_all_iff.mpr fun n : ℕ => ae_all_iff.mpr fun m : ℕ =>
    ae_ae_lintegral_tsum_exit_weighted_increment_ne_top hlp α hγ hγ2 (D := D n) isOpen_ball
      isBounded_ball m (hφc m) (hφ0 m) (hφ1 m)
      (fun z hz => greenPoleCutoff_zero_of_norm_lt (dyadicScale_pos m) hz)
  filter_upwards [hh.ae_tendsto_green_lintegral_smooth hγ hγ2 hα hμ,
    hh.ae_tendsto_green_mul_lintegral_smooth hγ hγ2 hα hμ, hsum,
    HarmonicBalls.ae_continuous_fieldCircleAverage hlp α, hF, hT,
    greenPotentialHolderStmt γ α hγ hγ2 hα Ω P hC hcirc μ hh hμ,
    hh.ae_singular_limit_and_approximant_ball_power hγ hγ2 hα hμ]
    with ω hgreen hgreenφ hsω hcω hFω hTω hHω hball
  intro O hO x hx
  have hcont (k : ℕ) : Continuous (fieldCircleAverage α (hcirc ω) (dyadicScale k)) :=
    hcω _ (dyadicScale_pos k)
  let V : Set ℂ → ℂ → ℝ≥0∞ := fun U y => ENNReal.ofReal (2 * ∫ z, greenFunction U y z ∂(μ ω))
  let Vφ : Set ℂ → ℕ → ℂ → ℝ≥0∞ := fun U m y =>
    ENNReal.ofReal (2 * ∫ z, greenFunction U y z * φ m z ∂(μ ω))
  -- the upper bound from every start
  have hup (U : Set ℂ) (hU : IsSmoothBoundedOpen U) (y : ℂ) (hy : y ∈ U) :
      expectedLBMExitTime (F ω y) U y ≤ V U y := by
    have h := expectedLBMExitTime_le_liminf_clockApprox_green hU hy hcont (hFω y) (hTω y)
    rwa [(hgreen U hU y).liminf_eq] at h
  -- continuity of the weighted Green potentials
  have hVφc (U : Set ℂ) (hU : IsSmoothBoundedOpen U) (m : ℕ) : ContinuousOn (Vφ U m) U := by
    have hmem : MemLp (φ m) ⊤ ((μ ω).restrict (closure U)) :=
      memLp_top_of_bound (hφc m).aestronglyMeasurable 1 (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 m z)]
        exact hφ1 m z)
    obtain ⟨-, C, r, hr, hHol⟩ := hHω U hU (φ m) hmem
    have hq : ContinuousOn (fun y => ∫ z in U, greenFunction U y z * φ m z ∂(μ ω)) U :=
      (hHol.continuousOn hr).mono subset_closure
    have heq (y : ℂ) : (∫ z in U, greenFunction U y z * φ m z ∂(μ ω)) =
        ∫ z, greenFunction U y z * φ m z ∂(μ ω) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        rw [greenFunction_of_notMem_right hz y, zero_mul]
    simp only [heq] at hq
    exact ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hq)
  -- the LQG measure has no atom at the insertion point
  have hatom : μ ω {0} = 0 := by
    obtain ⟨C, β, r₀, hC, hβ, hr₀, hb⟩ := hball 1
    have ht : Tendsto (fun s : ℝ => ENNReal.ofReal (C * s ^ β)) (𝓝[>] 0) (𝓝 0) := by
      have h := ((Real.continuous_rpow_const hβ.le).tendsto 0).const_mul C
      rw [Real.zero_rpow hβ.ne', mul_zero] at h
      have h' := ENNReal.tendsto_ofReal (h.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
      rwa [ENNReal.ofReal_zero] at h'
    refine le_antisymm (ge_of_tendsto ht ?_) zero_le
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hr₀)] with s hs hsr
    exact (measure_mono (singleton_subset_iff.mpr (mem_ball_self hs))).trans
      ((hb 0 (by simp) s hs (le_of_lt hsr)).1)
  -- a disc containing `O`
  obtain ⟨R, hR⟩ := hO.1.subset_ball (0 : ℂ)
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hOD : O ⊆ D n := hR.trans (ball_subset_ball (by linarith))
  have hxD : x ∈ D n := hOD hx
  -- the weighted lower bounds on the disc
  have hDlowφ (m : ℕ) : Vφ (D n) m x ≤ expectedLBMExitTime (F ω x) (D n) x := by
    refine le_expectedLBMExitTime_of_ae_lintegral_tsum_ne_top_of_le hcont (hDs n)
      (ψ := fun k z => φ m z * (dyadicScale (k + m) ^ (γ ^ 2 / 2) *
        Real.exp (γ * fieldCircleAverage α (hcirc ω) (dyadicScale (k + m)) z)))
      (fun k => (hφc m).mul (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul (hcont (k + m))))))
      (fun k z => mul_nonneg (hφ0 m z) (mul_nonneg (Real.rpow_nonneg (dyadicScale_pos _).le _)
        (Real.exp_pos _).le)) m
      (fun k z => mul_le_of_le_one_left (mul_nonneg (Real.rpow_nonneg (dyadicScale_pos _).le _)
        (Real.exp_pos _).le) (hφ1 m z)) (hsω n m) (V := Vφ (D n) m) ?_ hxD
      ((hVφc (D n) (hDs n) m) x hxD) (hFω x) (hTω x)
    intro y _
    exact (hgreenφ (D n) (hDs n) y (φ m) (hφc m) (hφ0 m) (hφ1 m)).comp (tendsto_add_atTop_nat m)
  -- removing the weights
  have hGint : Integrable (fun z => greenFunction (D n) x z) (μ ω) := by
    have h := (hHω (D n) (hDs n) (fun _ => (1 : ℝ)) (memLp_top_const 1)).1 x (subset_closure hxD)
    simp only [mul_one] at h
    exact h.integrable_of_forall_notMem_eq_zero fun z hz => greenFunction_of_notMem_right hz x
  have hlimφ : Tendsto (fun m => Vφ (D n) m x) atTop (𝓝 (V (D n) x)) := by
    refine ENNReal.tendsto_ofReal (Tendsto.const_mul 2 ?_)
    refine tendsto_integral_of_dominated_convergence (fun z => greenFunction (D n) x z)
      (fun m => ((measurable_greenFunction isOpen_ball x).mul (hφc m).measurable).aestronglyMeasurable)
      hGint (fun m => ae_of_all _ fun z => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (greenFunction_nonneg isBounded_ball x z),
        abs_of_nonneg (hφ0 m z)]
      exact mul_le_of_le_one_right (greenFunction_nonneg isBounded_ball x z) (hφ1 m z)
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hatom] with z hz
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_greenPoleCutoff_dyadicScale_eq_one hz] with m hm
      simp only [φ, hm, mul_one]
  have hDlow : V (D n) x ≤ expectedLBMExitTime (F ω x) (D n) x :=
    le_of_tendsto' hlimφ hDlowφ
  have hDeq : expectedLBMExitTime (F ω x) (D n) x = V (D n) x :=
    le_antisymm (hup _ (hDs n) x hxD) hDlow
  -- the comparison of `O` with the disc
  have hcomp := expectedLBMExitTime_le_add_sub_of_subset hcont hO (hDs n) hOD hx (hFω x)
    (hTω x) (hgreen (D n) (hDs n) x) (hgreen O hO x) ENNReal.ofReal_ne_top
  have hVle : V O x ≤ V (D n) x :=
    le_of_tendsto_of_tendsto' (hgreen O hO x) (hgreen (D n) (hDs n) x) fun k =>
      lintegral_mono fun z => by
        gcongr
        exact Section6.greenFunction_le_of_subset hOD isBounded_ball x z
  have hVfin : V (D n) x - V O x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top tsub_le_self
  have hlow : V O x ≤ expectedLBMExitTime (F ω x) O x := by
    rw [hDeq] at hcomp
    have h2 : (V (D n) x - V O x) + V O x ≤
        (V (D n) x - V O x) + expectedLBMExitTime (F ω x) O x := by
      rw [tsub_add_cancel_of_le hVle, add_comm]
      exact hcomp
    exact (ENNReal.add_le_add_iff_left hVfin).mp h2
  rw [le_antisymm (hup O hO x hx) hlow]
  rw [integral_mul_const, mul_comm, setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
    greenFunction_of_notMem_right hz x]

/-- **The LBM clause of Proposition 2.5 for time-change clocks.** For `0 < γ < 2` and `α < Q`,
for every family of LQG clocks from every start that are almost surely time-change clocks, for
almost every field, for every smooth bounded domain `O`, the expected exit time of Liouville
Brownian motion from `O` is finite from every start in `O` and Hölder continuous on `O`. -/
theorem ae_expectedLBMExitTime_lt_top_and_holder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < lqgQ γ) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ
      (fieldCircleAverage α (hcirc ω)) x (F ω x))
    (hT : ∀ᵐ ω ∂P, ∀ x : ℂ, ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F ω x b)) :
    ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O →
      (∀ x ∈ O, expectedLBMExitTime (F ω x) O x < ⊤) ∧
        ∃ C r : ℝ≥0, 0 < r ∧
          HolderOnWith C r (fun x => (expectedLBMExitTime (F ω x) O x).toReal) O := by
  filter_upwards [ae_forall_expectedLBMExitTime_eq_green hh hγ hγ2 hα hμ F hF hT,
    greenPotentialHolderStmt γ α hγ hγ2 hα Ω P hC hcirc μ hh hμ] with ω hid hHω
  intro O hO
  refine ⟨fun x hx => by rw [hid O hO x hx]; exact ENNReal.ofReal_lt_top, ?_⟩
  obtain ⟨-, C, r, hr, hHol⟩ := hHω O hO (fun _ => (2 : ℝ)) (memLp_top_const 2)
  refine ⟨C, r, hr, fun x hx y hy => ?_⟩
  have hnn (z : ℂ) : 0 ≤ ∫ w in O, greenFunction O z w * 2 ∂(μ ω) :=
    integral_nonneg fun w => mul_nonneg (greenFunction_nonneg hO.1 z w) (by norm_num)
  simp only [hid O hO x hx, hid O hO y hy, ENNReal.toReal_ofReal (hnn _)]
  exact hHol x (subset_closure hx) y (subset_closure hy)

/-- **The LBM clause of Proposition 2.5 from the positivity of the clock increments at the
origin.** For `0 < γ`, `γ² < 2` and `α < Q`, if for almost every field the dyadic lower limits
`G_{a,b}` of the clock increments are almost surely positive under Brownian motion from the
origin for all rationals `0 < a < b`, then for every family of LQG clocks from every start, for
almost every field, for every smooth bounded domain `O`, the expected exit time of Liouville
Brownian motion from `O` is finite from every start in `O` and Hölder continuous on `O`. -/
theorem ae_expectedLBMExitTime_lt_top_and_holder_of_dyadicIncrementLiminf_pos
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2)
    (hα : α < lqgQ γ) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hone : ∀ᵐ ω ∂P, ∀ a b : ℚ, 0 < a → a < b → ∀ᵐ w ∂(planarBrownianMotion 0),
      0 < dyadicIncrementLiminf γ (fieldCircleAverage α (hcirc ω)) a b w)
    (F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ
      (fieldCircleAverage α (hcirc ω)) x (F ω x)) :
    ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O →
      (∀ x ∈ O, expectedLBMExitTime (F ω x) O x < ⊤) ∧
        ∃ C r : ℝ≥0, 0 < r ∧
          HolderOnWith C r (fun x => (expectedLBMExitTime (F ω x) O x).toReal) O := by
  have hlp : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc :=
    (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  have hγ2' : γ < 2 := by nlinarith
  exact ae_expectedLBMExitTime_lt_top_and_holder hh hγ hγ2' hα hμ F hF
    (ae_forall_isTimeChangeClock_of_dyadicIncrementLiminf_pos hlp hγ hγ2 hα F hF hone)

end HarmonicBalls
