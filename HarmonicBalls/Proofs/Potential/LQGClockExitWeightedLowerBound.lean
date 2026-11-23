import HarmonicBalls.Proofs.Potential.LQGClockExitShiftLowerBound
import HarmonicBalls.Proofs.Potential.BrownianExpectedExitGreen

/-!
# Lower bound for expected exit times from every start by dominated clock approximations

This is the lower bound of `le_expectedLBMExitTime_of_ae_lintegral_tsum_ne_top` for general
continuous densities `ψ_k ≥ 0` dominated by the clock densities `ε^{γ²/2} e^{γ h_ε}` at the
scales `ε = 2^{-(k+m)}`. Let `J_k(b) = ∫_0^{τ_D} ψ_k(b_s) ds`. If for Lebesgue almost every start
`y ∈ D` the expected sum of the increments `|J_{k+2} - J_{k+1}|` is finite and the Green integrals
`∫ 2 G_D(y, z) ψ_k(z) dz` converge to `V(y)` for every `y ∈ D`, then `V(x) ≤ E_x[τ^{LBM}_D]` at
every `x ∈ D` where `V` is continuous within `D`. For a density `ψ_k` vanishing near the
insertion point the summability holds without any restriction on the insertion, and the bound
for the full clock follows by letting the excluded neighbourhood shrink.

The proof is that of the undominated case: dominated convergence from the summable increments
at almost every start, the comparison of the approximations of a path with those of the path
shifted by a time `s > 0`, the Markov property at time `s`, and `s → 0`. The approximations of
the clock are only used through the domination `J_k ≤ ∫_0^{τ_D} ε^{γ²/2} e^{γ h_ε(b_s)} ds`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- The occupation identity for a continuous nonnegative density: the expected integral of the
density along the path up to the exit time from a smooth bounded domain is its Green
integral. -/
theorem lintegral_exit_integral_eq_green {D : Set ℂ} (hD : IsSmoothBoundedOpen D) {x : ℂ}
    (hx : x ∈ D) {g : ℂ → ℝ} (hg : Continuous g) (hg0 : ∀ y, 0 ≤ g y) :
    (∫⁻ b, ENNReal.ofReal (∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal,
        g (b s.toNNReal)) ∂planarBrownianMotion x) =
      ∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) * ENNReal.ofReal (g y) := by
  let hDo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  have hocc := GreenOccupation.lintegral_occupationMeasure_eq_stopped_integral hDo hD.1 x hg hg0
  have hgreen := GreenOccupation.lintegral_brownian_occupation_eq_green_integral hD hx
    hg.measurable.ennreal_ofReal
  have hbefore := GreenOccupation.lintegral_occupationMeasure hDo x hg.measurable.ennreal_ofReal
  have h1 : (fun b : ContinuousPath ℂ => ENNReal.ofReal
      (∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, g (b s.toNNReal))) =
      fun p => ENNReal.ofReal (∫ t in (0 : ℝ)..((ContinuousPath.exitTime D p).toNNReal : ℝ),
        g (p (Real.toNNReal t))) := by
    funext b
    rw [ENNReal.coe_toNNReal_eq_toReal]
  rw [h1, ← hocc, hbefore, hgreen]

/-- The integral of a continuous density along the path up to the exit time is measurable in
the path. -/
theorem measurable_exit_integral {D : Set ℂ} (hD : IsOpen D) {g : ℂ → ℝ} (hg : Continuous g) :
    Measurable (fun b : ContinuousPath ℂ =>
      ∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, g (b s.toNNReal)) := by
  have h := (SubMarkovKernelSemigroup.stronglyMeasurable_feynmanKacAdditiveFunctional_joint
      hg.measurable).measurable.comp
      ((ContinuousPath.measurable_exitTime D hD).ennreal_toNNReal.prodMk measurable_id)
  have heq : (fun b : ContinuousPath ℂ =>
      ∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, g (b s.toNNReal)) =
      (fun p : ℝ≥0 × ContinuousPath ℂ =>
        SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional g p.1 p.2) ∘
        (fun b => ((ContinuousPath.exitTime D b).toNNReal, b)) := by
    funext b
    simp only [Function.comp_apply, SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional,
      ENNReal.coe_toNNReal_eq_toReal]
  rw [heq]
  exact h

/-- Before the exit time, the integral of a nonnegative continuous density up to the exit time
dominates the same integral for the path shifted by `s`. -/
theorem exit_integral_shift_le {g : ℂ → ℝ} (hg : Continuous g) (hg0 : ∀ y, 0 ≤ g y)
    (D : Set ℂ) (s : ℝ≥0) (b : ContinuousPath ℂ)
    (hs : (s : ℝ≥0∞) < ContinuousPath.exitTime D b) :
    (∫ u in (0 : ℝ)..(ContinuousPath.exitTime D (ContinuousPath.shift s b)).toReal,
        g ((ContinuousPath.shift s b) u.toNNReal)) ≤
      ∫ u in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, g (b u.toNNReal) := by
  have hadd := ContinuousPath.exitTime_shift_add D b s hs
  have hc : Continuous fun u : ℝ => g (b u.toNNReal) :=
    hg.comp (b.continuous.comp continuous_real_toNNReal)
  by_cases htop : ContinuousPath.exitTime D b = ⊤
  · have h' : ContinuousPath.exitTime D (ContinuousPath.shift s b) = ⊤ := by
      rw [htop] at hadd
      exact (ENNReal.add_eq_top.mp hadd).resolve_right ENNReal.coe_ne_top
    rw [htop, h', ENNReal.toReal_top, intervalIntegral.integral_same,
      intervalIntegral.integral_same]
  · have hτ' : ContinuousPath.exitTime D (ContinuousPath.shift s b) ≠ ⊤ := fun h =>
      htop (by rw [← hadd, h, top_add])
    have hreal : (ContinuousPath.exitTime D (ContinuousPath.shift s b)).toReal =
        (ContinuousPath.exitTime D b).toReal - s := by
      rw [← hadd, ENNReal.toReal_add hτ' ENNReal.coe_ne_top, ENNReal.coe_toReal]
      ring
    have hsτ : (s : ℝ) ≤ (ContinuousPath.exitTime D b).toReal := by
      have h := ENNReal.toReal_mono htop hs.le
      rwa [ENNReal.coe_toReal] at h
    rw [hreal]
    have h1 := intervalIntegral.integral_comp_add_left (fun v => g (b v.toNNReal)) (s : ℝ)
      (a := 0) (b := (ContinuousPath.exitTime D b).toReal - s)
    rw [add_zero, add_sub_cancel] at h1
    have heq : (∫ u in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal - s,
        g ((ContinuousPath.shift s b) u.toNNReal)) =
        ∫ u in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal - s, g (b ((s : ℝ) + u).toNNReal) := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le (sub_nonneg.mpr hsτ)] at hu
      simp only [ContinuousPath.shift_apply, Real.toNNReal_add s.coe_nonneg hu.1,
        Real.toNNReal_coe]
    rw [heq, h1]
    exact intervalIntegral.integral_mono_interval s.coe_nonneg hsτ le_rfl
      (Eventually.of_forall fun v => hg0 _) (hc.intervalIntegrable _ _)

/-- Summable expected increments of the integrals of continuous nonnegative densities up to the
exit time give the convergence of their expectations to the expectation of their lower limit. -/
theorem tendsto_lintegral_exit_integral_liminf_of_tsum_ne_top {ψ : ℕ → ℂ → ℝ}
    (hψc : ∀ k, Continuous (ψ k)) (hψ0 : ∀ k z, 0 ≤ ψ k z) {D : Set ℂ}
    (hD : IsSmoothBoundedOpen D) {y : ℂ} (hy : y ∈ D)
    (hsum : (∫⁻ b, ∑' k, ENNReal.ofReal
      |(∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, ψ (k+2) (b s.toNNReal)) -
        ∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, ψ (k+1) (b s.toNNReal)|
      ∂(planarBrownianMotion y)) ≠ ⊤) :
    Tendsto (fun k : ℕ => ∫⁻ b, ENNReal.ofReal
        (∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, ψ k (b s.toNNReal))
        ∂(planarBrownianMotion y)) atTop
      (𝓝 (∫⁻ b, liminf (fun k : ℕ => ENNReal.ofReal
        (∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, ψ k (b s.toNNReal))) atTop
        ∂(planarBrownianMotion y))) := by
  have hDo : IsOpen D := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  let μ := planarBrownianMotion y
  let A : ℕ → ContinuousPath ℂ → ℝ := fun k b =>
    ∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, ψ k (b s.toNNReal)
  have hAm (k : ℕ) : Measurable (A k) := measurable_exit_integral hDo (hψc k)
  have hA0 (k : ℕ) (b : ContinuousPath ℂ) : 0 ≤ A k b :=
    intervalIntegral.integral_nonneg ENNReal.toReal_nonneg fun _ _ => hψ0 k _
  let S : ContinuousPath ℂ → ℝ≥0∞ := fun b => ∑' k, ENNReal.ofReal |A (k+2) b - A (k+1) b|
  have hSm : Measurable S := Measurable.tsum fun k =>
    (((hAm (k+2)).sub (hAm (k+1))).abs).ennreal_ofReal
  -- domination by the first approximation and the total variation
  have hdom (b : ContinuousPath ℂ) (k : ℕ) : ENNReal.ofReal (A (k+1) b) ≤
      ENNReal.ofReal (A 1 b) + ∑ j ∈ Finset.range k, ENNReal.ofReal |A (j+2) b - A (j+1) b| := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ← add_assoc]
      calc ENNReal.ofReal (A (k + 2) b) ≤
          ENNReal.ofReal (A (k+1) b) + ENNReal.ofReal |A (k+2) b - A (k+1) b| := by
            rw [← ENNReal.ofReal_add (hA0 _ _) (abs_nonneg _)]
            apply ENNReal.ofReal_le_ofReal
            have := le_abs_self (A (k+2) b - A (k+1) b)
            linarith
        _ ≤ _ := add_le_add ih le_rfl
  have hdomS (b : ContinuousPath ℂ) (k : ℕ) : ENNReal.ofReal (A (k+1) b) ≤
      ENNReal.ofReal (A 1 b) + S b :=
    (hdom b k).trans (add_le_add le_rfl (ENNReal.sum_le_tsum _))
  let Z : ContinuousPath ℂ → ℝ≥0∞ := fun b => liminf (fun k => ENNReal.ofReal (A k b)) atTop
  have hlim : ∀ᵐ b ∂μ, Tendsto (fun k => ENNReal.ofReal (A (k+1) b)) atTop (𝓝 (Z b)) := by
    filter_upwards [ae_lt_top hSm hsum] with b hb
    obtain ⟨l, hl⟩ := exists_tendsto_of_tsum_ofReal_abs_sub_ne_top (a := fun k => A k b) hb.ne
    have h := ENNReal.tendsto_ofReal hl
    have hZ : Z b = ENNReal.ofReal l := h.liminf_eq
    rw [hZ]
    exact h.comp (tendsto_add_atTop_nat 1)
  have hA1fin : (∫⁻ b, ENNReal.ofReal (A 1 b) ∂μ) ≠ ⊤ := by
    rw [lintegral_exit_integral_eq_green hD hy (hψc 1) (hψ0 1)]
    obtain ⟨M, hM⟩ := hD.1.isCompact_closure.exists_bound_of_continuousOn (hψc 1).continuousOn
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := max M 0))
      (GreenOccupation.lintegral_green_density_lt_top hD y).ne) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ D
    · rw [mul_comm]
      gcongr
      have h := hM z (subset_closure hz)
      rw [Real.norm_eq_abs, abs_of_nonneg (hψ0 1 z)] at h
      exact h.trans (le_max_left _ _)
    · rw [greenFunction_of_notMem_right hz y]
      simp
  have hdc := tendsto_lintegral_of_dominated_convergence (fun b => ENNReal.ofReal (A 1 b) + S b)
    (fun k => (hAm (k+1)).ennreal_ofReal) (fun k => Eventually.of_forall fun b => hdomS b k)
    (by
      rw [lintegral_add_left (hAm 1).ennreal_ofReal]
      exact ENNReal.add_ne_top.mpr ⟨hA1fin, hsum⟩) hlim
  exact (tendsto_add_atTop_iff_nat 1).mp hdc

/-- **Lower bound for the expected exit time from every start, with dominated densities.** Let
`ψ_k` be continuous nonnegative densities with `ψ_k ≤ ε^{γ²/2} e^{γ h_ε}` at `ε = 2^{-(k+m)}`. If
for Lebesgue almost every start in a smooth bounded domain `D` the expected sum of the absolute
increments of the integrals of `ψ_k` up to the exit time is finite, and the Green integrals of
`ψ_k` converge to `V(y)` for every `y ∈ D`, then for every start `x ∈ D` at which `V` is
continuous within `D` and every LQG clock from `x` that is almost surely a time-change clock,
`V(x)` is at most the expected exit time of Liouville Brownian motion from `D`. -/
theorem le_expectedLBMExitTime_of_ae_lintegral_tsum_ne_top_of_le {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    (hεc : ∀ k : ℕ, Continuous (hε (dyadicScale k))) {D : Set ℂ} (hD : IsSmoothBoundedOpen D)
    {ψ : ℕ → ℂ → ℝ} (hψc : ∀ k, Continuous (ψ k)) (hψ0 : ∀ k z, 0 ≤ ψ k z) (m : ℕ)
    (hψle : ∀ k z, ψ k z ≤
      dyadicScale (k + m) ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale (k + m)) z))
    (hsum : ∀ᵐ y ∂(volume.restrict D), (∫⁻ b, ∑' k, ENNReal.ofReal
      |(∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, ψ (k+2) (b s.toNNReal)) -
        ∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, ψ (k+1) (b s.toNNReal)|
      ∂(planarBrownianMotion y)) ≠ ⊤)
    {V : ℂ → ℝ≥0∞}
    (hV : ∀ y ∈ D, Tendsto (fun k : ℕ => ∫⁻ z, ENNReal.ofReal (2 * greenFunction D y z) *
      ENNReal.ofReal (ψ k z)) atTop (𝓝 (V y)))
    {x : ℂ} (hx : x ∈ D) (hVx : ContinuousWithinAt V D x)
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hclock : IsLQGClock planarBrownianMotion γ hε x F)
    (hF : ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F b)) :
    V x ≤ expectedLBMExitTime F D x := by
  have hDo : IsOpen D := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  have hDb : Bornology.IsBounded D := hD.1
  let J : ℕ → ContinuousPath ℂ → ℝ := fun k b =>
    ∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, ψ k (b s.toNNReal)
  have hJm (k : ℕ) : Measurable (J k) := measurable_exit_integral hDo (hψc k)
  let Jf : ℕ → ContinuousPath ℂ → ℝ := fun k b =>
    lqgClockApprox γ hε (dyadicScale k) b (ContinuousPath.exitTime D b).toNNReal
  have hJJf (k : ℕ) (b : ContinuousPath ℂ) : J k b ≤ Jf (k + m) b := by
    have e : Jf (k + m) b = ∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal,
        dyadicScale (k + m) ^ (γ ^ 2 / 2) *
          Real.exp (γ * hε (dyadicScale (k + m)) (b s.toNNReal)) := by
      simp only [Jf, lqgClockApprox, ENNReal.coe_toNNReal_eq_toReal]
    rw [e]
    exact intervalIntegral.integral_mono_on ENNReal.toReal_nonneg
      (((hψc k).comp (b.continuous.comp continuous_real_toNNReal)).intervalIntegrable _ _)
      ((continuous_dyadicIncrementIntegrand (hεc (k + m)) b).intervalIntegrable _ _)
      fun s _ => hψle k _
  let Z : ContinuousPath ℂ → ℝ≥0∞ := fun w => liminf (fun k => ENNReal.ofReal (J k w)) atTop
  have hZm : Measurable Z := Measurable.liminf fun k => (hJm k).ennreal_ofReal
  let S : ContinuousPath ℂ → ℝ≥0∞ := fun w => ∑' k, ENNReal.ofReal |J (k+2) w - J (k+1) w|
  have hSm : Measurable S := Measurable.tsum fun k =>
    (((hJm (k+2)).sub (hJm (k+1))).abs).ennreal_ofReal
  let E : Set (ContinuousPath ℂ) := {w | S w ≠ ⊤}
  have hEm : MeasurableSet E := (hSm (measurableSet_singleton ⊤)).compl
  have hconvE : ∀ w ∈ E, Tendsto (fun k => ENNReal.ofReal (J k w)) atTop (𝓝 (Z w)) := by
    intro w hw
    obtain ⟨l, hl⟩ := exists_tendsto_of_tsum_ofReal_abs_sub_ne_top (a := fun k => J k w) hw
    have h := ENNReal.tendsto_ofReal hl
    have hZ : Z w = ENNReal.ofReal l := h.liminf_eq
    rw [hZ]
    exact h
  have hsum' := (ae_restrict_iff' hDo.measurableSet).mp hsum
  have hEae : ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ w ∂(planarBrownianMotion y), w ∈ E := by
    filter_upwards [hsum'] with y hy
    by_cases hyD : y ∈ D
    · exact (ae_lt_top hSm (hy hyD)).mono fun w hw => hw.ne
    · filter_upwards [ae_planarBrownianMotion_eval_zero y] with w hw
      have hτ0 : ContinuousPath.exitTime D w = 0 := by
        by_contra hne
        exact hyD (hw ▸ (ContinuousPath.exitTime_pos_iff D hDo w).mp (pos_iff_ne_zero.mpr hne))
      show S w ≠ ⊤
      simp [S, J, hτ0]
  have hgood : ∀ᵐ y ∂(volume : Measure ℂ), y ∈ D →
      V y ≤ ∫⁻ w, Z w ∂(planarBrownianMotion y) := by
    filter_upwards [hsum'] with y hy hyD
    have hlim := tendsto_lintegral_exit_integral_liminf_of_tsum_ne_top hψc hψ0 hD hyD (hy hyD)
    have hgreen (k : ℕ) : (∫⁻ b, ENNReal.ofReal (J k b) ∂(planarBrownianMotion y)) =
        ∫⁻ z, ENNReal.ofReal (2 * greenFunction D y z) * ENNReal.ofReal (ψ k z) :=
      lintegral_exit_integral_eq_green hD hyD (hψc k) (hψ0 k)
    exact (tendsto_nhds_unique (hV y hyD) (hlim.congr hgreen)).le
  have hconv : TendstoInMeasure (planarBrownianMotion x) Jf atTop
      (fun b => (lbmExitTime F D b).toReal) := by
    apply tendstoInMeasure_iff_dist.mpr
    intro η hη
    simpa only [Jf, Real.dist_eq] using
      hclock.tendsto_measure_clockApprox_lbmExitTime hDo hDb hF hη
  obtain ⟨ns, hns, hns_ae⟩ := (hconv.comp (tendsto_add_atTop_nat m)).exists_seq_tendsto_ae
  have hfin : ∀ᵐ b ∂(planarBrownianMotion x), lbmExitTime F D b ≠ ⊤ := by
    filter_upwards [hF, Section6.ae_planarBrownian_exitTime_bounded_lt_top x hDb] with b hb hτ
    rw [lbmExitTime_eq_clockValue hDo hb hτ.ne]
    exact ENNReal.coe_ne_top
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
      have h1 : Tendsto (fun j => ENNReal.ofReal (Jf (ns j + m) b)) atTop
          (𝓝 (lbmExitTime F D b)) := by
        have h := ENNReal.tendsto_ofReal hb
        rwa [ENNReal.ofReal_toReal hbfin] at h
      have h2 : Tendsto (fun j => ENNReal.ofReal (J (ns j) (ContinuousPath.shift s b))) atTop
          (𝓝 (Z (ContinuousPath.shift s b))) := (hconvE _ hbE).comp hns.tendsto_atTop
      exact le_of_tendsto_of_tendsto' h2 h1 fun j => ENNReal.ofReal_le_ofReal
        ((exit_integral_shift_le (hψc _) (hψ0 _) D s b hbA).trans (hJJf _ b))
    · rw [indicator_of_notMem
        (show b ∉ {b | (s : ℝ≥0∞) < ContinuousPath.exitTime D b} from hbA)]
      exact zero_le
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
