import HarmonicBalls.Proofs.Potential.LQGClockExpectationConvergence
import HarmonicBalls.Proofs.Potential.LQGClockExitQuenchedUniformIntegrability
import HarmonicBalls.Proofs.Potential.LQGClockEveryStart
import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveUniformL1

/-!
# Lower bound for expected exit times from every start by the Markov property

Let `D` be a smooth bounded domain and `J_k(b)` the clock approximations at the dyadic scales,
read at the exit time of the path `b` from `D`. Suppose that for Lebesgue almost every start
`y ∈ D` the expected sum of the absolute increments `|J_{k+2} - J_{k+1}|` under Brownian motion
from `y` is finite. For such `y` the approximations converge almost surely and in `L¹` to a
limit `Z`, a functional of the path alone, so `E_y[Z]` is the limit `V(y)` of the expected Green
integrals of the approximating measures.

For a start `x ∈ D` and a time `s > 0`, on the event `{s < τ_D}` the clock approximations of a
path dominate those of the path shifted by `s`. Along a subsequence the approximations converge
almost surely to the exit time of Liouville Brownian motion, and the approximations of the
shifted path converge to `Z` of the shifted path: the law of the path after time `s` is a mixture
of Brownian laws over the law of the position at time `s`, which is absolutely continuous. The
Markov property at time `s` then gives `E_x[τ^{LBM}_D] ≥ E_x[V(b_s); s < τ_D]`, and letting
`s → 0`, continuity of `V` at `x` within `D` gives `V(x) ≤ E_x[τ^{LBM}_D]` for every start `x`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- A real sequence whose successive increments have finite total variation converges. -/
theorem exists_tendsto_of_tsum_ofReal_abs_sub_ne_top {a : ℕ → ℝ}
    (h : (∑' k, ENNReal.ofReal |a (k+2) - a (k+1)|) ≠ ⊤) : ∃ l, Tendsto a atTop (𝓝 l) := by
  have hc : CauchySeq (fun n => a (n+1)) := by
    refine cauchySeq_of_edist_le_of_tsum_ne_top
      (fun k => ENNReal.ofReal |a (k+2) - a (k+1)|) (fun n => ?_) h
    rw [edist_dist, Real.dist_eq, abs_sub_comm]
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨l, (tendsto_add_atTop_iff_nat 1).mp hl⟩

/-- Summable expected increments give the convergence of the expected exit-time clock
approximations to the expectation of their lower limit. -/
theorem tendsto_lintegral_exit_clockApprox_liminf_of_tsum_ne_top {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    (hεc : ∀ k : ℕ, Continuous (hε (dyadicScale k))) {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (y : ℂ)
    (hsum : (∫⁻ b, ∑' k, ENNReal.ofReal
      |lqgClockApprox γ hε (dyadicScale (k+2)) b (ContinuousPath.exitTime D b).toNNReal -
        lqgClockApprox γ hε (dyadicScale (k+1)) b (ContinuousPath.exitTime D b).toNNReal|
      ∂(planarBrownianMotion y)) ≠ ⊤) :
    Tendsto (fun k : ℕ => ∫⁻ b, ENNReal.ofReal (lqgClockApprox γ hε (dyadicScale k) b
        (ContinuousPath.exitTime D b).toNNReal) ∂(planarBrownianMotion y)) atTop
      (𝓝 (∫⁻ b, liminf (fun k : ℕ => ENNReal.ofReal (lqgClockApprox γ hε (dyadicScale k) b
        (ContinuousPath.exitTime D b).toNNReal)) atTop ∂(planarBrownianMotion y))) := by
  let μ := planarBrownianMotion y
  let A : ℕ → ContinuousPath ℂ → ℝ := fun k b =>
    lqgClockApprox γ hε (dyadicScale k) b (ContinuousPath.exitTime D b).toNNReal
  have hAm (k : ℕ) : Measurable (A k) := measurable_lqgClockApprox_exit hD k (hεc k)
  have hA0 (k : ℕ) (b : ContinuousPath ℂ) : 0 ≤ A k b :=
    intervalIntegral.integral_nonneg_of_forall (NNReal.coe_nonneg _) fun _ =>
      mul_nonneg (Real.rpow_nonneg (dyadicScale_pos k).le _) (Real.exp_pos _).le
  have hui : UniformIntegrable A 1 μ :=
    uniformIntegrable_exit_clockApprox_of_lintegral_tsum_ne_top hεc hD hDb y hsum
  let S : ContinuousPath ℂ → ℝ≥0∞ := fun b => ∑' k, ENNReal.ofReal |A (k+2) b - A (k+1) b|
  have hSm : Measurable S := Measurable.tsum fun k =>
    (((hAm (k+2)).sub (hAm (k+1))).abs).ennreal_ofReal
  have hSfin : ∀ᵐ b ∂μ, S b ≠ ⊤ := (ae_lt_top hSm hsum).mono fun _ h => h.ne
  let Z : ContinuousPath ℂ → ℝ≥0∞ := fun b => liminf (fun k => ENNReal.ofReal (A k b)) atTop
  let L : ContinuousPath ℂ → ℝ := fun b => (Z b).toReal
  have hlim : ∀ᵐ b ∂μ, Tendsto (fun k => A k b) atTop (𝓝 (L b)) ∧
      ENNReal.ofReal (L b) = Z b := by
    filter_upwards [hSfin] with b hb
    obtain ⟨l, hl⟩ := exists_tendsto_of_tsum_ofReal_abs_sub_ne_top (a := fun k => A k b) hb
    have hl0 : 0 ≤ l := ge_of_tendsto' hl fun k => hA0 k b
    have hZ : Z b = ENNReal.ofReal l := (ENNReal.tendsto_ofReal hl).liminf_eq
    have hL : L b = l := by simp only [L, hZ, ENNReal.toReal_ofReal hl0]
    refine ⟨?_, ?_⟩
    · rw [hL]
      exact hl
    · rw [hL, hZ]
  have hconv : TendstoInMeasure μ A atTop L :=
    tendstoInMeasure_of_tendsto_ae (fun k => (hAm k).aestronglyMeasurable)
      (hlim.mono fun _ h => h.1)
  have hL : Integrable L μ := hui.integrable_of_tendstoInMeasure hconv
  have hAi (k : ℕ) : Integrable (A k) μ := memLp_one_iff_integrable.mp (hui.memLp k)
  have hLp : Tendsto (fun k => eLpNorm (A k - L) 1 μ) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
      (fun k => (hAi k).aestronglyMeasurable) (memLp_one_iff_integrable.mpr hL)
      hui.unifIntegrable hconv
  have hint : Tendsto (fun k => ∫ b, A k b ∂μ) atTop (𝓝 (∫ b, L b ∂μ)) :=
    tendsto_integral_of_L1' L (Eventually.of_forall hAi) hLp
  have hE (k : ℕ) : ENNReal.ofReal (∫ b, A k b ∂μ) = ∫⁻ b, ENNReal.ofReal (A k b) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal (hAi k) (Eventually.of_forall (hA0 k))
  have hEL : ENNReal.ofReal (∫ b, L b ∂μ) = ∫⁻ b, Z b ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hL
      (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)]
    exact lintegral_congr_ae (hlim.mono fun _ h => h.2)
  have h := ENNReal.tendsto_ofReal hint
  rw [hEL] at h
  exact h.congr hE

/-- Before the exit time, the clock approximation read at the exit time dominates the clock
approximation of the path shifted by `s` read at its own exit time. -/
theorem lqgClockApprox_exit_shift_le {γ : ℝ} {hε : ℝ → ℂ → ℝ} {k : ℕ}
    (hc : Continuous (hε (dyadicScale k))) (D : Set ℂ) (s : ℝ≥0) (b : ContinuousPath ℂ)
    (hs : (s : ℝ≥0∞) < ContinuousPath.exitTime D b) :
    lqgClockApprox γ hε (dyadicScale k) (ContinuousPath.shift s b)
        (ContinuousPath.exitTime D (ContinuousPath.shift s b)).toNNReal ≤
      lqgClockApprox γ hε (dyadicScale k) b (ContinuousPath.exitTime D b).toNNReal := by
  have hadd := ContinuousPath.exitTime_shift_add D b s hs
  have e (w : ContinuousPath ℂ) (t : ℝ≥0∞) : lqgClockApprox γ hε (dyadicScale k) w t.toNNReal =
      dyadicIncrementApprox γ hε k 0 t.toReal w := by
    rw [← ENNReal.coe_toNNReal_eq_toReal]
    rfl
  by_cases htop : ContinuousPath.exitTime D b = ⊤
  · have h' : ContinuousPath.exitTime D (ContinuousPath.shift s b) = ⊤ := by
      rw [htop] at hadd
      exact (ENNReal.add_eq_top.mp hadd).resolve_right ENNReal.coe_ne_top
    rw [htop, h', ENNReal.toNNReal_top, lqgClockApprox_zero, lqgClockApprox_zero]
  · have hτ' : ContinuousPath.exitTime D (ContinuousPath.shift s b) ≠ ⊤ := fun h =>
      htop (by rw [← hadd, h, top_add])
    have hreal : (ContinuousPath.exitTime D (ContinuousPath.shift s b)).toReal =
        (ContinuousPath.exitTime D b).toReal - s := by
      rw [← hadd, ENNReal.toReal_add hτ' ENNReal.coe_ne_top, ENNReal.coe_toReal]
      ring
    have hsτ : (s : ℝ) ≤ (ContinuousPath.exitTime D b).toReal := by
      have h := ENNReal.toReal_mono htop hs.le
      rwa [ENNReal.coe_toReal] at h
    rw [e, e, hreal]
    have hsh := dyadicIncrementApprox_shift γ hε k (a := (s : ℝ))
      (b := (ContinuousPath.exitTime D b).toReal) s.coe_nonneg hsτ b
    rw [Real.toNNReal_coe] at hsh
    rw [← hsh]
    exact dyadicIncrementApprox_mono hc b s.coe_nonneg hsτ le_rfl

/-- The law of planar Brownian motion at a positive time is absolutely continuous. -/
theorem planarHeatSemigroup_kernel_absolutelyContinuous (x : ℂ) {t : ℝ≥0} (ht : t ≠ 0) :
    planarHeatSemigroup.kernel t x ≪ volume := by
  rw [planarHeatSemigroup_apply]
  have h := (gaussianReal_absolutelyContinuous x.re ht).prod
    (gaussianReal_absolutelyContinuous x.im ht)
  have hm := h.map Complex.measurableEquivRealProd.symm.measurable
  rw [← Measure.volume_eq_prod ℝ ℝ, Complex.volume_preserving_equiv_real_prod.symm.map_eq] at hm
  exact hm

/-- An event of paths that holds almost surely from Lebesgue almost every start holds almost
surely, from every start, for the path shifted by a positive time. -/
theorem ae_shift_mem_of_ae_volume {s : ℝ≥0} (hs : s ≠ 0) {E : Set (ContinuousPath ℂ)}
    (hE : MeasurableSet E)
    (h : ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ w ∂(planarBrownianMotion y), w ∈ E) (x : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion x), ContinuousPath.shift s b ∈ E := by
  let K := SubMarkovKernelSemigroup.IsConservative.continuousProcess
    planarHeatSemigroup isConservative_planarHeatSemigroup
  have hmap : (planarBrownianMotion x).map (ContinuousPath.shift s) =
      K ∘ₘ planarHeatSemigroup.kernel s x := by
    rw [planarBrownianMotion_eq_continuousProcess]
    have hshift := congrArg (fun K => K x)
      (SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_shift
        planarHeatSemigroup isConservative_planarHeatSemigroup
        isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup s)
    rw [Kernel.map_apply _ (ContinuousPath.measurable_shift_fixed s) x,
      Kernel.comp_apply] at hshift
    exact hshift
  have ha : ∀ᵐ w ∂((planarBrownianMotion x).map (ContinuousPath.shift s)), w ∈ E := by
    rw [hmap]
    refine Measure.ae_comp_of_ae_ae hE ?_
    filter_upwards [(planarHeatSemigroup_kernel_absolutelyContinuous x hs).ae_le h] with y hy
    show ∀ᵐ w ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess
      planarHeatSemigroup isConservative_planarHeatSemigroup y), w ∈ E
    rw [← planarBrownianMotion_eq_continuousProcess]
    exact hy
  exact (ae_map_iff (ContinuousPath.measurable_shift_fixed s).aemeasurable hE).mp ha

/-- The Markov property at a deterministic time `s`: on an event of the canonical filtration at
time `s`, the expectation of a functional of the shifted path is the expectation of its mean
under Brownian motion from the position at time `s`. -/
theorem setLIntegral_shift_eq {s : ℝ≥0} {A : Set (ContinuousPath ℂ)}
    (hA : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) s] A)
    {Z : ContinuousPath ℂ → ℝ≥0∞} (hZ : Measurable Z) (x : ℂ) :
    ∫⁻ b in A, Z (ContinuousPath.shift s b) ∂(planarBrownianMotion x) =
      ∫⁻ b in A, (∫⁻ w, Z w ∂(planarBrownianMotion (b s))) ∂(planarBrownianMotion x) := by
  have hres := SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_restrict_map_shift
    planarHeatSemigroup isConservative_planarHeatSemigroup
    isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup x s A hA
  rw [← planarBrownianMotion_eq_continuousProcess] at hres
  rw [← lintegral_map hZ (ContinuousPath.measurable_shift_fixed s), hres,
    Measure.lintegral_bind (Kernel.aemeasurable _) hZ.aemeasurable]
  simp only [Kernel.comap_apply]
  rfl

/-- **Lower bound for the expected exit time from every start.** If for Lebesgue almost every
start in a smooth bounded domain `D` the expected sum of the absolute increments of the
exit-time clock approximations is finite, and the expected Green integrals of the approximating
measures converge to `V(y)` for every `y ∈ D`, then for every start `x ∈ D` at which `V` is
continuous within `D` and every LQG clock from `x` that is almost surely a time-change clock,
`V(x)` is at most the expected exit time of Liouville Brownian motion from `D`. -/
theorem le_expectedLBMExitTime_of_ae_lintegral_tsum_ne_top {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    (hεc : ∀ k : ℕ, Continuous (hε (dyadicScale k))) {D : Set ℂ} (hD : IsSmoothBoundedOpen D)
    (hsum : ∀ᵐ y ∂(volume.restrict D), (∫⁻ b, ∑' k, ENNReal.ofReal
      |lqgClockApprox γ hε (dyadicScale (k+2)) b (ContinuousPath.exitTime D b).toNNReal -
        lqgClockApprox γ hε (dyadicScale (k+1)) b (ContinuousPath.exitTime D b).toNNReal|
      ∂(planarBrownianMotion y)) ≠ ⊤)
    {V : ℂ → ℝ≥0∞}
    (hV : ∀ y ∈ D, Tendsto (fun k : ℕ => ∫⁻ z, ENNReal.ofReal (2 * greenFunction D y z) *
      ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) z)))
      atTop (𝓝 (V y)))
    {x : ℂ} (hx : x ∈ D) (hVx : ContinuousWithinAt V D x)
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hclock : IsLQGClock planarBrownianMotion γ hε x F)
    (hF : ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F b)) :
    V x ≤ expectedLBMExitTime F D x := by
  have hDo : IsOpen D := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  have hDb : Bornology.IsBounded D := hD.1
  let J : ℕ → ContinuousPath ℂ → ℝ := fun k b =>
    lqgClockApprox γ hε (dyadicScale k) b (ContinuousPath.exitTime D b).toNNReal
  have hJm (k : ℕ) : Measurable (J k) := measurable_lqgClockApprox_exit hDo k (hεc k)
  let Z : ContinuousPath ℂ → ℝ≥0∞ := fun w => liminf (fun k => ENNReal.ofReal (J k w)) atTop
  have hZm : Measurable Z := Measurable.liminf fun k => (hJm k).ennreal_ofReal
  let S : ContinuousPath ℂ → ℝ≥0∞ := fun w => ∑' k, ENNReal.ofReal |J (k+2) w - J (k+1) w|
  have hSm : Measurable S := Measurable.tsum fun k =>
    (((hJm (k+2)).sub (hJm (k+1))).abs).ennreal_ofReal
  let E : Set (ContinuousPath ℂ) := {w | S w ≠ ⊤}
  have hEm : MeasurableSet E := (hSm (measurableSet_singleton ⊤)).compl
  -- on `E` the approximations converge to `Z`
  have hconvE : ∀ w ∈ E, Tendsto (fun k => ENNReal.ofReal (J k w)) atTop (𝓝 (Z w)) := by
    intro w hw
    obtain ⟨l, hl⟩ := exists_tendsto_of_tsum_ofReal_abs_sub_ne_top (a := fun k => J k w) hw
    have h := ENNReal.tendsto_ofReal hl
    have hZ : Z w = ENNReal.ofReal l := h.liminf_eq
    rw [hZ]
    exact h
  have hsum' := (ae_restrict_iff' hDo.measurableSet).mp hsum
  -- from Lebesgue almost every start the path lies in `E` almost surely
  have hEae : ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ w ∂(planarBrownianMotion y), w ∈ E := by
    filter_upwards [hsum'] with y hy
    by_cases hyD : y ∈ D
    · exact (ae_lt_top hSm (hy hyD)).mono fun w hw => hw.ne
    · filter_upwards [ae_planarBrownianMotion_eval_zero y] with w hw
      have hτ0 : ContinuousPath.exitTime D w = 0 := by
        by_contra hne
        exact hyD (hw ▸ (ContinuousPath.exitTime_pos_iff D hDo w).mp (pos_iff_ne_zero.mpr hne))
      show S w ≠ ⊤
      simp [S, J, hτ0, lqgClockApprox_zero]
  -- at Lebesgue almost every start in `D` the mean of `Z` is `V`
  have hgood : ∀ᵐ y ∂(volume : Measure ℂ), y ∈ D →
      V y ≤ ∫⁻ w, Z w ∂(planarBrownianMotion y) := by
    filter_upwards [hsum'] with y hy hyD
    have hlim := tendsto_lintegral_exit_clockApprox_liminf_of_tsum_ne_top hεc hDo hDb y (hy hyD)
    have hgreen (k : ℕ) : (∫⁻ b, ENNReal.ofReal (J k b) ∂(planarBrownianMotion y)) =
        ∫⁻ z, ENNReal.ofReal (2 * greenFunction D y z) *
          ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) z)) :=
      (GreenOccupation.lintegral_lqgClockApprox_exit_eq_occupation_and_green hD hyD γ
        (dyadicScale k) (dyadicScale_pos k) hε (hεc k)).2
    exact (tendsto_nhds_unique (hV y hyD) (hlim.congr hgreen)).le
  -- the approximations from `x` converge in probability to the exit time of LBM
  have hconv : TendstoInMeasure (planarBrownianMotion x) J atTop
      (fun b => (lbmExitTime F D b).toReal) := by
    apply tendstoInMeasure_iff_dist.mpr
    intro η hη
    simpa only [J, Real.dist_eq] using
      hclock.tendsto_measure_clockApprox_lbmExitTime hDo hDb hF hη
  obtain ⟨ns, hns, hns_ae⟩ := hconv.exists_seq_tendsto_ae
  have hfin : ∀ᵐ b ∂(planarBrownianMotion x), lbmExitTime F D b ≠ ⊤ := by
    filter_upwards [hF, Section6.ae_planarBrownian_exitTime_bounded_lt_top x hDb] with b hb hτ
    rw [lbmExitTime_eq_clockValue hDo hb hτ.ne]
    exact ENNReal.coe_ne_top
  -- the Markov property at a positive time `s`
  have hbound : ∀ s : ℝ≥0, s ≠ 0 →
      (∫⁻ b in {b | (s : ℝ≥0∞) < ContinuousPath.exitTime D b},
        (∫⁻ w, Z w ∂(planarBrownianMotion (b s))) ∂(planarBrownianMotion x)) ≤
        expectedLBMExitTime F D x := by
    intro s hs
    have hA := ContinuousPath.measurableSet_lt_exitTime_canonicalFiltration D hDo s
    rw [← setLIntegral_shift_eq hA hZm x,
      ← lintegral_indicator (ContinuousPath.measurableSet_lt_exitTime D hDo s)]
    unfold expectedLBMExitTime
    apply lintegral_mono_ae
    filter_upwards [hns_ae, hfin, ae_shift_mem_of_ae_volume hs hEm hEae x] with b hb hbfin hbE
    by_cases hbA : (s : ℝ≥0∞) < ContinuousPath.exitTime D b
    · rw [indicator_of_mem (show b ∈ {b | (s : ℝ≥0∞) < ContinuousPath.exitTime D b} from hbA)]
      have h1 : Tendsto (fun j => ENNReal.ofReal (J (ns j) b)) atTop
          (𝓝 (lbmExitTime F D b)) := by
        have h := ENNReal.tendsto_ofReal hb
        rwa [ENNReal.ofReal_toReal hbfin] at h
      have h2 : Tendsto (fun j => ENNReal.ofReal (J (ns j) (ContinuousPath.shift s b))) atTop
          (𝓝 (Z (ContinuousPath.shift s b))) := (hconvE _ hbE).comp hns.tendsto_atTop
      exact le_of_tendsto_of_tendsto' h2 h1 fun j =>
        ENNReal.ofReal_le_ofReal (lqgClockApprox_exit_shift_le (hεc _) D s b hbA)
    · rw [indicator_of_notMem
        (show b ∉ {b | (s : ℝ≥0∞) < ContinuousPath.exitTime D b} from hbA)]
      exact zero_le
  -- letting `s → 0`
  by_contra hlt
  obtain ⟨c, hcu, hcV⟩ := exists_between (not_le.mp hlt)
  obtain ⟨δ, hδ, hδV⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp (hVx (isOpen_Ioi.mem_nhds hcV)))
  let s : ℕ → ℝ≥0 := fun m => ⟨1 / ((m : ℝ) + 1), by positivity⟩
  have hs0 (m : ℕ) : s m ≠ 0 := by
    rw [← NNReal.coe_ne_zero]
    show 1 / ((m : ℝ) + 1) ≠ 0
    positivity
  have hst : Tendsto s atTop (𝓝 0) := by
    rw [← NNReal.tendsto_coe]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  let Sm : ℕ → Set (ContinuousPath ℂ) := fun m =>
    {b | (s m : ℝ≥0∞) < ContinuousPath.exitTime D b} ∩ {b | dist (b (s m)) x < δ}
  have hSmm (m : ℕ) : MeasurableSet (Sm m) :=
    (ContinuousPath.measurableSet_lt_exitTime D hDo (s m)).inter
      (measurableSet_lt ((ContinuousPath.measurable_coordinateProcess (s m)).dist
        measurable_const) measurable_const)
  have hle (m : ℕ) : c * planarBrownianMotion x (Sm m) ≤ expectedLBMExitTime F D x := by
    refine le_trans ?_ (hbound (s m) (hs0 m))
    rw [← lintegral_indicator_const (hSmm m),
      ← lintegral_indicator (ContinuousPath.measurableSet_lt_exitTime D hDo (s m))]
    apply lintegral_mono_ae
    have hgx := ae_of_ae_map (ContinuousPath.measurable_coordinateProcess (s m)).aemeasurable
      ((planarBrownianMotion_map_eval_absolutelyContinuous x (s m) (hs0 m)).ae_le hgood)
    filter_upwards [hgx] with b hb
    by_cases hbS : b ∈ Sm m
    · rw [indicator_of_mem hbS, indicator_of_mem hbS.1]
      have hbD : b (s m) ∈ D := ContinuousPath.mem_of_lt_exitTime D b (s m) hbS.1
      exact (hδV hbS.2 hbD).le.trans (hb hbD)
    · rw [indicator_of_notMem hbS]
      exact zero_le
  have hP1 : Tendsto (fun m => planarBrownianMotion x (Sm m)) atTop (𝓝 1) := by
    have hlim : ∀ᵐ b ∂(planarBrownianMotion x), Tendsto
        (fun m => (Sm m).indicator (fun _ => (1 : ℝ≥0∞)) b) atTop (𝓝 1) := by
      filter_upwards [ae_planarBrownianMotion_eval_zero x] with b hb0
      have hτpos : 0 < ContinuousPath.exitTime D b :=
        (ContinuousPath.exitTime_pos_iff D hDo b).mpr (hb0 ▸ hx)
      have h1 : ∀ᶠ m in atTop, (s m : ℝ≥0∞) < ContinuousPath.exitTime D b := by
        have h := ENNReal.tendsto_coe.mpr hst
        rw [ENNReal.coe_zero] at h
        exact h.eventually (gt_mem_nhds hτpos)
      have h2 : ∀ᶠ m in atTop, dist (b (s m)) x < δ := by
        have hc := (b.continuous.tendsto 0).comp hst
        rw [hb0] at hc
        exact (Metric.tendsto_nhds.mp hc) δ hδ
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [h1, h2] with m hm1 hm2
      rw [indicator_of_mem (show b ∈ Sm m from ⟨hm1, hm2⟩)]
    have h := tendsto_lintegral_of_dominated_convergence (fun _ => (1 : ℝ≥0∞))
      (f := fun _ => (1 : ℝ≥0∞))
      (fun m => measurable_const.indicator (hSmm m))
      (fun m => Eventually.of_forall fun b => by
        by_cases hb : b ∈ Sm m <;> simp [hb])
      (by simp) hlim
    rw [lintegral_const, measure_univ, mul_one] at h
    refine h.congr fun m => ?_
    rw [lintegral_indicator_const (hSmm m), one_mul]
  have hlimc : Tendsto (fun m => c * planarBrownianMotion x (Sm m)) atTop (𝓝 (c * 1)) :=
    ENNReal.Tendsto.const_mul hP1 (Or.inl one_ne_zero)
  rw [mul_one] at hlimc
  exact absurd (le_of_tendsto' hlimc hle) (not_le.mpr hcu)

end HarmonicBalls
