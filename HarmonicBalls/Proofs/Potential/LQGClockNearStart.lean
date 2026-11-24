import HarmonicBalls.Proofs.Potential.GreenOccupationCharacterization
import HarmonicBalls.Proofs.Potential.LQGUniformGreenTail
import HarmonicBalls.Defs.Brownian

/-!
# The approximate LQG clocks are small at small times, uniformly in the scale

Let `g k ≥ 0` be continuous densities whose measures `ν_k = g_k(z) dz` satisfy one ball bound
`ν_k(B_t(x)) ≤ C t^β` for `0 < t < r₀`, uniformly in `k`. Then for every `η, θ > 0` there is a
time `a > 0` such that, for planar Brownian motion `w` started at `x`,
`P_x[∫_0^a g_k(w_s) ds ≥ η] ≤ θ` for every `k`.

Proof. For a small radius `ρ`, let `τ` be the exit time of `w` from `O = B_ρ(x)`. On `{τ > a}`
the integral up to time `a` is at most the occupation integral `∫_0^τ g_k(w_s) ds`, whose
expectation is `∫ 2 G_O(x, y) ν_k(dy)` (`lintegral_brownian_occupation_eq_green_integral`). The
ball bound makes this at most a constant times `ρ^{β/4}`, uniformly in `k`
(`green_integral_ball_le_of_local_mass_growth`), so Markov's inequality bounds the second event.
The exit time from `B_ρ(x)` of a continuous path started at `x` is positive, so
`P_x[τ ≤ a] → 0` as `a → 0`.

The densities of the circle-average approximations of the LQG measure satisfy the ball bound
almost surely, for every centre and uniformly in the dyadic scale
(`IsWholePlaneGFF.ae_singular_approximant_ball_power_all_disks`).
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Metric MarkovProcess
open scoped ENNReal NNReal

open scoped ContDiff in
/-- A disc of positive radius is a smooth bounded open set: `‖z - c‖² - r²` is a smooth
nondegenerate defining function. -/
theorem isSmoothBoundedOpen_ball_of_pos (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsSmoothBoundedOpen (ball c r) := by
  let ρ : ℂ → ℝ := fun z => ‖z - c‖ ^ 2 - r ^ 2
  refine ⟨isBounded_ball, ρ, ?_, ?_, ?_⟩
  · exact ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const
  · ext z
    simp only [mem_ball, dist_eq_norm, mem_ofPred_eq, ρ]
    have hn := norm_nonneg (z - c)
    constructor <;> intro h <;> nlinarith [sq_nonneg (‖z - c‖ - r)]
  · intro z hz hzero
    have hn : 0 < ‖z - c‖ ^ 2 := by dsimp [ρ] at hz; nlinarith [sq_pos_of_pos hr]
    have hd := congrArg (fun L : ℂ →L[ℝ] ℝ => L (z - c)) hzero
    have hf : HasFDerivAt ρ (2 • (innerSL ℝ (z - c)).comp
        (ContinuousLinearMap.id ℝ ℂ)) z := by
      exact (((hasFDerivAt_id z).sub_const c).norm_sq).sub_const _
    rw [hf.fderiv] at hd
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, inner_self_eq_norm_sq_to_K,
      zero_apply, nsmul_eq_mul] at hd
    exact (mul_ne_zero (by norm_num) (by exact_mod_cast (ne_of_gt hn))) hd

/-- A continuous path started in an open set stays in it for a positive time. -/
theorem exists_pos_le_exitTime_of_mem {U : Set ℂ} (hU : IsOpen U) {w : ContinuousPath ℂ}
    (hw : w 0 ∈ U) : ∃ δ : ℝ≥0, 0 < δ ∧ (δ : ℝ≥0∞) ≤ ContinuousPath.exitTime U w := by
  have hnhds : w ⁻¹' U ∈ 𝓝 (0 : ℝ≥0) := w.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hw)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  refine ⟨⟨ε, hε.le⟩, by exact_mod_cast hε, ?_⟩
  rw [ContinuousPath.le_exitTime_iff]
  intro v hv
  by_contra hlt
  have h1 : v < (⟨ε, hε.le⟩ : ℝ≥0) := ENNReal.coe_lt_coe.1 (not_le.1 hlt)
  have hv' : (v : ℝ) < ε := NNReal.coe_lt_coe.2 h1
  refine hv (hball ?_)
  rw [mem_ball, NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg v)]
  exact hv'

/-- Planar Brownian motion started at `x` leaves the disc `B_ρ(x)` before time `1/(n+1)` with
probability tending to `0`. -/
theorem tendsto_planarBrownianMotion_exitTime_ball_le (x : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun n : ℕ => planarBrownianMotion x
      {w | ContinuousPath.exitTime (ball x ρ) w ≤ ((((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ≥0∞)})
      atTop (𝓝 0) := by
  set s : ℕ → Set (ContinuousPath ℂ) := fun n =>
    {w | ContinuousPath.exitTime (ball x ρ) w ≤ ((((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ≥0∞)} with hs
  have hmeas : ∀ n, MeasurableSet (s n) := fun n =>
    measurableSet_le (ContinuousPath.measurable_exitTime _ isOpen_ball) measurable_const
  have hanti : Antitone s := by
    intro m n hmn w hw
    simp only [hs, mem_ofPred_eq] at hw ⊢
    refine le_trans hw ?_
    have h1 : ((m : ℝ≥0) + 1) ≤ (n : ℝ≥0) + 1 := by gcongr
    exact_mod_cast inv_anti₀ (by positivity) h1
  have hlim := tendsto_measure_iInter_atTop (μ := planarBrownianMotion x)
    (fun n => (hmeas n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have hzero : planarBrownianMotion x (⋂ n, s n) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 (ae_planarBrownianMotion_eval_zero x))
    intro w hw h0
    simp only [hs, mem_iInter, mem_ofPred_eq] at hw
    obtain ⟨δ, hδ, hδτ⟩ := exists_pos_le_exitTime_of_mem isOpen_ball
      (show w 0 ∈ ball x ρ by rw [h0]; exact mem_ball_self hρ)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < δ by exact_mod_cast hδ)
    have hn' : (((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) < δ := by
      rw [← NNReal.coe_lt_coe]
      push_cast
      simpa [one_div] using hn
    exact absurd ((hδτ.trans (hw n)).trans_lt (by exact_mod_cast hn')) (lt_irrefl _)
  rwa [Function.comp_def, hzero] at hlim

/-- Before the exit time, the time integral of a continuous density up to a fixed time is at
most the occupation integral up to the exit time. -/
theorem ofReal_intervalIntegral_le_occupation {D : Set ℂ} {g : ℂ → ℝ} (hg : Continuous g)
    (hg0 : ∀ z, 0 ≤ g z) (w : ContinuousPath ℂ) {a : ℝ≥0}
    (ha : (a : ℝ≥0∞) < ContinuousPath.exitTime D w) :
    ENNReal.ofReal (∫ s in (0 : ℝ)..(a : ℝ), g (w s.toNNReal)) ≤
      ∫⁻ t in Ioi (0 : ℝ),
        {t : ℝ | ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D w}.indicator
          (fun t => ENNReal.ofReal (g (w (Real.toNNReal t)))) t := by
  have hcont : Continuous fun s : ℝ => g (w s.toNNReal) :=
    hg.comp (w.continuous.comp continuous_real_toNNReal)
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg a), ofReal_integral_eq_lintegral_ofReal
    ((hcont.integrableOn_Icc (a := (0 : ℝ)) (b := (a : ℝ))).mono_set Ioc_subset_Icc_self)
    (ae_of_all _ fun _ => hg0 _)]
  have hsub : Ioc (0 : ℝ) a ⊆
      {t : ℝ | ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D w} := by
    intro t ht
    have : Real.toNNReal t ≤ a := Real.toNNReal_le_iff_le_coe.2 ht.2
    exact lt_of_le_of_lt (by exact_mod_cast this) ha
  calc ∫⁻ t in Ioc (0 : ℝ) a, ENNReal.ofReal (g (w t.toNNReal))
      = ∫⁻ t in Ioi (0 : ℝ), (Ioc (0 : ℝ) a).indicator
          (fun t => ENNReal.ofReal (g (w (Real.toNNReal t)))) t := by
        rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
          inter_eq_left.2 Ioc_subset_Ioi_self]
    _ ≤ _ := lintegral_mono fun t => indicator_le_indicator_of_subset hsub (fun _ => zero_le) t

/-- The occupation integral up to the exit time is a measurable function of the path. -/
theorem measurable_occupation_exitTime {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ≥0∞}
    (hf : Measurable f) :
    Measurable fun w : ContinuousPath ℂ => ∫⁻ t in Ioi (0 : ℝ),
      {t : ℝ | ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D w}.indicator
        (fun t => f (w (Real.toNNReal t))) t := by
  have heval : Measurable fun p : ℝ × ContinuousPath ℂ ↦ p.2 (Real.toNNReal p.1) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hS : MeasurableSet {p : ℝ × ContinuousPath ℂ |
      ((Real.toNNReal p.1 : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D p.2} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp (measurable_real_toNNReal.comp measurable_fst))
      ((ContinuousPath.measurable_exitTime D hD).comp measurable_snd)
  have hF : Measurable fun p : ℝ × ContinuousPath ℂ =>
      {p : ℝ × ContinuousPath ℂ |
        ((Real.toNNReal p.1 : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D p.2}.indicator
        (fun p => f (p.2 (Real.toNNReal p.1))) p := (hf.comp heval).indicator hS
  convert hF.lintegral_prod_left' (μ := volume.restrict (Ioi (0 : ℝ))) using 1
  funext w
  congr 1

/-- **Small times give small approximate clocks, uniformly in the scale.** -/
theorem exists_pos_time_measure_clock_ge_le {x : ℂ} {g : ℕ → ℂ → ℝ} (hg : ∀ k, Continuous (g k))
    (hg0 : ∀ k z, 0 ≤ g k z) {C β r₀ : ℝ} (hC : 0 < C) (hβ : 0 < β) (hr₀ : 0 < r₀)
    (hball : ∀ k, ∀ t, 0 < t → t < r₀ →
      volume.withDensity (fun z => ENNReal.ofReal (g k z)) (ball x t) ≤ ENNReal.ofReal (C * t ^ β))
    {η θ : ℝ} (hη : 0 < η) (hθ : 0 < θ) :
    ∃ a : ℝ≥0, 0 < a ∧ ∀ k, planarBrownianMotion x
      {w | η ≤ ∫ s in (0 : ℝ)..(a : ℝ), g k (w s.toNNReal)} ≤ ENNReal.ofReal θ := by
  set R : ℝ := ‖x‖ + 2 with hRdef
  have hR : 0 < R := by positivity
  set K₁ : ℝ := (2 * Real.pi)⁻¹ * ((β / 4)⁻¹ * (2 * R) ^ (β / 4)) with hK₁
  set K₂ : ℝ := C * (r₀ / 4) ^ β + (C * ((2 : ℝ) ^ β + 1)) * ((2 * (β / 4)) / (β - 2 * (β / 4)))
    with hK₂
  -- the radius `ρ`
  have hcont : Tendsto (fun ρ : ℝ => K₁ * K₂ * ρ ^ (β / 4)) (𝓝[>] 0) (𝓝 0) := by
    have h := ((Real.continuousAt_rpow_const 0 (β / 4) (Or.inr (by positivity))).tendsto).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [Real.zero_rpow (by positivity)] at h
    simpa using h.const_mul (K₁ * K₂)
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (K₁ * K₂ * ρ ^ (β / 4) < θ * η / 4 ∧
      ρ < min (r₀ / 4) 1) ∧ 0 < ρ :=
    ((hcont.eventually (gt_mem_nhds (by positivity))).and
      (Ioo_mem_nhdsGT (lt_min (by positivity) one_pos))).and self_mem_nhdsWithin |>.mono
      fun ρ h => ⟨⟨h.1.1, h.1.2.2⟩, h.2⟩
  obtain ⟨ρ, ⟨hρK, hρlt⟩, hρ⟩ := hev.exists
  have hρr : ρ ≤ r₀ / 4 := (hρlt.trans_le (min_le_left _ _)).le
  have hρ1 : ρ < 1 := hρlt.trans_le (min_le_right _ _)
  have hOs : IsSmoothBoundedOpen (ball x ρ) := isSmoothBoundedOpen_ball_of_pos x hρ
  have hxO : x ∈ ball x ρ := mem_ball_self hρ
  have hOR : ball x ρ ⊆ ball (0 : ℂ) R := by
    intro z hz
    rw [mem_ball, dist_zero_right]
    have := norm_sub_norm_le z x
    rw [mem_ball, dist_eq_norm] at hz
    linarith
  -- the expected occupation integrals
  set Φ : ℕ → ContinuousPath ℂ → ℝ≥0∞ := fun k w => ∫⁻ t in Ioi (0 : ℝ),
    {t : ℝ | ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime (ball x ρ) w}.indicator
      (fun t => ENNReal.ofReal (g k (w (Real.toNNReal t)))) t with hΦ
  have hocc : ∀ k, ∫⁻ w, Φ k w ∂(planarBrownianMotion x) ≤
      ENNReal.ofReal (2 * (K₁ * K₂ * ρ ^ (β / 4))) := by
    intro k
    have hfm : Measurable fun y => ENNReal.ofReal (g k y) := (hg k).measurable.ennreal_ofReal
    rw [hΦ, GreenOccupation.lintegral_brownian_occupation_eq_green_integral hOs hxO hfm]
    set ν : Measure ℂ := volume.withDensity (fun z => ENNReal.ofReal (g k z)) with hν
    obtain ⟨hint, hbd⟩ := green_integral_ball_le_of_local_mass_growth isOpen_ball hR hOR hC hβ hr₀ x ν
      (hball k) hρ hρr
    have hG0 : ∀ y, 0 ≤ greenFunction (ball x ρ) x y := greenFunction_nonneg isBounded_ball x
    have hGout : ∀ y, y ∉ ball x ρ → greenFunction (ball x ρ) x y = 0 :=
      fun y hy => greenFunction_of_notMem_right hy x
    have hGm : AEMeasurable (fun y => ENNReal.ofReal (2 * greenFunction (ball x ρ) x y)) volume :=
      ((integrable_greenFunction_pole (GreenGeneral.isOpen_of_isSmoothBoundedOpen hOs) hOs.1 x).const_mul
        2).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    calc ∫⁻ y, ENNReal.ofReal (2 * greenFunction (ball x ρ) x y) * ENNReal.ofReal (g k y)
        = ∫⁻ y, ENNReal.ofReal (2 * greenFunction (ball x ρ) x y) ∂ν := by
          rw [hν, lintegral_withDensity_eq_lintegral_mul₀ (μ := volume) hfm.aemeasurable hGm]
          refine lintegral_congr fun y => ?_
          simp only [Pi.mul_apply]
          rw [mul_comm]
      _ = ∫⁻ y in ball x ρ, ENNReal.ofReal (2 * greenFunction (ball x ρ) x y) ∂ν := by
          rw [← lintegral_indicator measurableSet_ball]
          refine lintegral_congr fun y => ?_
          by_cases hy : y ∈ ball x ρ
          · simp [hy]
          · simp [hy, hGout y hy]
      _ = ENNReal.ofReal (∫ y in ball x ρ, 2 * greenFunction (ball x ρ) x y ∂ν) :=
          (ofReal_integral_eq_lintegral_ofReal (hint.const_mul 2)
            (ae_of_all _ fun y => mul_nonneg zero_le_two (hG0 y))).symm
      _ ≤ ENNReal.ofReal (2 * (K₁ * K₂ * ρ ^ (β / 4))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_const_mul]
          refine mul_le_mul_of_nonneg_left (hbd.trans_eq ?_) zero_le_two
          rw [hK₁, hK₂]
          ring
  -- the time `a`
  obtain ⟨n, hn⟩ := ENNReal.tendsto_atTop_zero.1 (tendsto_planarBrownianMotion_exitTime_ball_le x hρ)
    (ENNReal.ofReal (θ / 2)) (by simp; positivity)
  replace hn := hn n le_rfl
  refine ⟨((n : ℝ≥0) + 1)⁻¹, by positivity, fun k => ?_⟩
  set a : ℝ≥0 := ((n : ℝ≥0) + 1)⁻¹ with ha
  have hsub : {w : ContinuousPath ℂ | η ≤ ∫ s in (0 : ℝ)..(a : ℝ), g k (w s.toNNReal)} ⊆
      {w | ContinuousPath.exitTime (ball x ρ) w ≤ (a : ℝ≥0∞)} ∪ {w | ENNReal.ofReal η ≤ Φ k w} := by
    intro w hw
    by_cases hτ : ContinuousPath.exitTime (ball x ρ) w ≤ (a : ℝ≥0∞)
    · exact Or.inl hτ
    · right
      exact (ENNReal.ofReal_le_ofReal hw).trans
        (ofReal_intervalIntegral_le_occupation (hg k) (hg0 k) w (not_le.1 hτ))
  have hΦm : Measurable (Φ k) :=
    measurable_occupation_exitTime isOpen_ball (hg k).measurable.ennreal_ofReal
  have hηne : ENNReal.ofReal η ≠ 0 := by simpa using hη
  calc planarBrownianMotion x {w | η ≤ ∫ s in (0 : ℝ)..(a : ℝ), g k (w s.toNNReal)}
      ≤ planarBrownianMotion x ({w | ContinuousPath.exitTime (ball x ρ) w ≤ (a : ℝ≥0∞)} ∪
          {w | ENNReal.ofReal η ≤ Φ k w}) := measure_mono hsub
    _ ≤ planarBrownianMotion x {w | ContinuousPath.exitTime (ball x ρ) w ≤ (a : ℝ≥0∞)} +
          planarBrownianMotion x {w | ENNReal.ofReal η ≤ Φ k w} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (θ / 2) + (∫⁻ w, Φ k w ∂(planarBrownianMotion x)) / ENNReal.ofReal η :=
        add_le_add hn (meas_ge_le_lintegral_div hΦm.aemeasurable hηne ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (2 * (K₁ * K₂ * ρ ^ (β / 4))) / ENNReal.ofReal η :=
        add_le_add le_rfl (ENNReal.div_le_div_right (hocc k) _)
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) := by
        refine add_le_add le_rfl ?_
        rw [← ENNReal.ofReal_div_of_pos hη]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ hη]
        nlinarith
    _ = ENNReal.ofReal θ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

end HarmonicBalls
