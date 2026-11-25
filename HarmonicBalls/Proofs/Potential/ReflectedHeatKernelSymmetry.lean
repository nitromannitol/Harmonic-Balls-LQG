import HarmonicBalls.Proofs.Potential.ReflectedClockGreenBound
import HarmonicBalls.Proofs.Potential.LaplaceTransformUniqueness
import HarmonicBalls.Proofs.Potential.ReflectedHeatKernelL2Semigroup
import HarmonicBalls.Proofs.Potential.ReflectedHeatKernelUniqueness

/-!
# Symmetry of the heat kernel of the time change

Let `A` be a clock of reflected Brownian motion in `K₀` with finite Revuz measure `ν`, carried by
`K₀`, without atoms in `K₀`, with full support in `K₀` and closed-ball bounds, and let `p'` be a
heat kernel of the time change, continuous on `(0, ∞) × K₀ × K₀`. Then
`p'(t, x, y) = p'(t, y, x)` for `t > 0` and `x, y ∈ K₀` (`isLBMHeatKernel_symm`).

* Letting `β ↓ 0` in the symmetry of the killed resolvents (`lintegral_mul_clockResolvent_comm`,
  with the potential bound `exists_clockGreen_one_le`) gives the symmetry of the resolvent
  `R_c f(x) = E_x ∫_0^∞ e^{-c u} f(Y_u) du` (`lintegral_mul_clockResolvent_zero_comm`), by
  monotone convergence.
* `⟨1_E, R_c 1_F⟩_ν = ∫_0^∞ e^{-c u} φ_{E,F}(u) du` with
  `φ_{E,F}(u) = ∫_{E ∩ K₀} ∫_{F ∩ K₀} p'(u, x, y) ν(dy) ν(dx)`, continuous and bounded on
  `(0, ∞)`; uniqueness of the Laplace transform (`eqOn_Ioi_of_laplace_eq`) gives
  `φ_{E,F} = φ_{F,E}`, and full support with continuity in the space variables gives the
  symmetry of `p'` (`eqOn_of_forall_setLIntegral_eq`, twice).

This is the argument of the answer to the question on reflected clock positivity, part (c),
following Fukushima–Oshima–Takeda, *Dirichlet forms and symmetric Markov processes*, 2nd ed.
2011, Theorem 6.2.1.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess Metric
open scoped ENNReal NNReal

namespace HarmonicBalls

/-! ### Letting the killing rate tend to zero -/

theorem monotone_ofReal_exp_neg_inv_succ_mul {s : ℝ} (hs : 0 ≤ s) :
    Monotone fun n : ℕ => ENNReal.ofReal (Real.exp (-(1 / ((n : ℝ) + 1) * s))) := by
  intro m n hmn
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg
    (mul_le_mul_of_nonneg_right ?_ hs)))
  have : (m : ℝ) ≤ n := by exact_mod_cast hmn
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem iSup_ofReal_exp_neg_inv_succ_mul {s : ℝ} (hs : 0 ≤ s) :
    ⨆ n : ℕ, ENNReal.ofReal (Real.exp (-(1 / ((n : ℝ) + 1) * s))) = 1 := by
  refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 ?_)) ?_
  · have : 0 ≤ 1 / ((n : ℝ) + 1) * s := by positivity
    linarith
  · have h0 : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1) * s)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const s).neg
      simpa using this
    have h1 := (Real.continuous_exp.tendsto 0).comp h0
    rw [Real.exp_zero] at h1
    have h2 := (ENNReal.continuous_ofReal.tendsto 1).comp h1
    rw [ENNReal.ofReal_one] at h2
    exact le_of_tendsto' h2 fun n => le_iSup (fun n : ℕ =>
      ENNReal.ofReal (Real.exp (-(1 / ((n : ℝ) + 1) * s)))) n

theorem monotone_resolventOccupation_inv_succ (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (c : ℝ)
    (f : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) :
    Monotone fun n : ℕ => resolventOccupation A (1 / ((n : ℝ) + 1)) c f b := by
  intro m n hmn
  refine lintegral_mono fun u => mul_le_mul' le_rfl (mul_le_mul' ?_ le_rfl)
  exact monotone_ofReal_exp_neg_inv_succ_mul (NNReal.coe_nonneg _) hmn

theorem resolventOccupation_zero_eq_iSup {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (c : ℝ) {f : ℂ → ℝ≥0∞} (hf : Measurable f)
    (b : ContinuousPath ℂ) :
    resolventOccupation A 0 c f b = ⨆ n : ℕ, resolventOccupation A (1 / ((n : ℝ) + 1)) c f b := by
  have hφ := measurable_clockInverse_timeChange_uncurry hA
  have hmeas : ∀ n : ℕ, Measurable fun u : ℝ => ENNReal.ofReal (Real.exp (-(c * u))) *
      discountWeight (1 / ((n : ℝ) + 1)) f
        ((pcafClockInverse (clockRationalRegularization A) u.toNNReal b : ℝ),
          unitSquareTimeChangeRegularized A u.toNNReal b) := fun n =>
    (measurable_exp_neg_mul c).mul ((measurable_discountWeight _ hf).comp
      (hφ.comp measurable_prodMk_left))
  have hmono : Monotone fun (n : ℕ) (u : ℝ) => ENNReal.ofReal (Real.exp (-(c * u))) *
      discountWeight (1 / ((n : ℝ) + 1)) f
        ((pcafClockInverse (clockRationalRegularization A) u.toNNReal b : ℝ),
          unitSquareTimeChangeRegularized A u.toNNReal b) := fun m n hmn u =>
    mul_le_mul' le_rfl (mul_le_mul' (monotone_ofReal_exp_neg_inv_succ_mul
      (NNReal.coe_nonneg _) hmn) le_rfl)
  calc resolventOccupation A 0 c f b
      = ∫⁻ u in Ioi (0 : ℝ), ⨆ n : ℕ, ENNReal.ofReal (Real.exp (-(c * u))) *
          discountWeight (1 / ((n : ℝ) + 1)) f
            ((pcafClockInverse (clockRationalRegularization A) u.toNNReal b : ℝ),
              unitSquareTimeChangeRegularized A u.toNNReal b) := by
        refine lintegral_congr fun u => ?_
        simp only [discountWeight, zero_mul, neg_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul]
        rw [← ENNReal.mul_iSup, ← ENNReal.iSup_mul,
          iSup_ofReal_exp_neg_inv_succ_mul (NNReal.coe_nonneg _), one_mul]
    _ = ⨆ n : ℕ, resolventOccupation A (1 / ((n : ℝ) + 1)) c f b := lintegral_iSup hmeas hmono

theorem clockResolvent_zero_eq_iSup {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (c : ℝ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) (x : ℂ) :
    clockResolvent A 0 c f x = ⨆ n : ℕ, clockResolvent A (1 / ((n : ℝ) + 1)) c f x := by
  unfold clockResolvent
  simp_rw [resolventOccupation_zero_eq_iSup hA c hf]
  exact lintegral_iSup (fun n => measurable_resolventOccupation hA _ c hf)
    fun m n hmn b => monotone_resolventOccupation_inv_succ A c f b hmn

/-- **Symmetry of the resolvent of the time change**: `⟨f, R_c h⟩_ν = ⟨h, R_c f⟩_ν` for
measurable `f ≥ 0` and `0 ≤ h ≤ 1`, with `R_c h(x) = E_x ∫_0^∞ e^{-c u} h(Y_u) du`. -/
theorem lintegral_mul_clockResolvent_zero_comm {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A)
    (hU : ∀ z ∈ closedSquare 0 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun t => A t b) atTop atTop) [IsFiniteMeasure (unitSquareRevuzMeasure A)]
    (hνK : unitSquareRevuzMeasure A (closedSquare 0 1)ᶜ = 0)
    (hatom : ∀ y ∈ closedSquare 0 1, unitSquareRevuzMeasure A {y} = 0)
    {m A' β' : ℝ} (hm : 0 ≤ m) (hA' : 0 ≤ A') (hβ' : 0 < β')
    (hmass : unitSquareRevuzMeasure A univ ≤ ENNReal.ofReal m)
    (hball : ∀ y ∈ closedSquare 0 1, ∀ ρ : ℝ, 0 < ρ →
      unitSquareRevuzMeasure A (closedBall y ρ) ≤ ENNReal.ofReal (A' * ρ ^ β'))
    {c : ℝ} (hc : 0 ≤ c) {h f : ℂ → ℝ≥0∞} (hh : Measurable h) (hf : Measurable f)
    (hh1 : ∀ x, h x ≤ 1) :
    ∫⁻ x, f x * clockResolvent A 0 c h x ∂unitSquareRevuzMeasure A =
      ∫⁻ x, h x * clockResolvent A 0 c f x ∂unitSquareRevuzMeasure A := by
  obtain ⟨L, hL, hLb⟩ := exists_lintegral_clockOccupation_window_le hA hU hνK hatom hm hA' hβ'
    hmass hball
  have hsymm : ∀ n : ℕ, ∫⁻ x, f x * clockResolvent A (1 / ((n : ℝ) + 1)) c h x
      ∂unitSquareRevuzMeasure A = ∫⁻ x, h x * clockResolvent A (1 / ((n : ℝ) + 1)) c f x
        ∂unitSquareRevuzMeasure A := by
    intro n
    obtain ⟨C, hC, hCb⟩ := exists_clockGreen_one_le hA hU hνK hL hLb
      (β := 1 / ((n : ℝ) + 1)) (by positivity)
    exact lintegral_mul_clockResolvent_comm hA hU hνK _ hc hC hCb hh hf hh1
  have hlim : ∀ {g k : ℂ → ℝ≥0∞}, Measurable g → Measurable k →
      ∫⁻ x, g x * clockResolvent A 0 c k x ∂unitSquareRevuzMeasure A =
        ⨆ n : ℕ, ∫⁻ x, g x * clockResolvent A (1 / ((n : ℝ) + 1)) c k x
          ∂unitSquareRevuzMeasure A := by
    intro g k hg hk
    simp_rw [clockResolvent_zero_eq_iSup hA.measurable c hk, ENNReal.mul_iSup]
    exact lintegral_iSup (fun n => hg.mul (measurable_clockResolvent hA.measurable _ c hk))
      fun m n hmn x => mul_le_mul' le_rfl (lintegral_mono fun b =>
        monotone_resolventOccupation_inv_succ A c k b hmn)
  rw [hlim hf hh, hlim hh hf]
  exact iSup_congr hsymm

/-! ### The resolvent as a Laplace transform -/

theorem measurable_timeChangeRegularized_uncurry {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) :
    Measurable fun p : ContinuousPath ℂ × ℝ => unitSquareTimeChangeRegularized A p.2.toNNReal p.1 :=
  (measurable_clockInverse_timeChange_uncurry hA).snd

/-- `R_c 1_F(x) = ∫_0^∞ e^{-c u} P_x(Y_u ∈ F) du`. -/
theorem clockResolvent_zero_indicator_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (c : ℝ) {F : Set ℂ} (hF : MeasurableSet F) (x : ℂ) :
    clockResolvent A 0 c (F.indicator 1) x = ∫⁻ u in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(c * u))) * reflectedPlanarBrownianMotion 0 1 x
        (unitSquareTimeChangeRegularized A u.toNNReal ⁻¹' F) := by
  have hφ := measurable_clockInverse_timeChange_uncurry hA
  have hY := measurable_timeChangeRegularized_uncurry hA
  have hd := measurable_discountWeight 0 (measurable_one.indicator hF)
  have hmeas : Measurable fun p : ContinuousPath ℂ × ℝ => ENNReal.ofReal (Real.exp (-(c * p.2))) *
      discountWeight 0 (F.indicator 1)
        ((pcafClockInverse (clockRationalRegularization A) p.2.toNNReal p.1 : ℝ),
          unitSquareTimeChangeRegularized A p.2.toNNReal p.1) :=
    ((measurable_exp_neg_mul c).comp measurable_snd).mul (hd.comp hφ)
  have h1 : clockResolvent A 0 c (F.indicator 1) x = ∫⁻ (b : ContinuousPath ℂ),
      (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(c * u))) * discountWeight 0 (F.indicator 1)
        ((pcafClockInverse (clockRationalRegularization A) u.toNNReal b : ℝ),
          unitSquareTimeChangeRegularized A u.toNNReal b)) ∂reflectedPlanarBrownianMotion 0 1 x :=
    rfl
  rw [h1, lintegral_lintegral_swap (by exact hmeas.aemeasurable)]
  refine lintegral_congr fun u => ?_
  have hYu : Measurable (unitSquareTimeChangeRegularized A u.toNNReal) :=
    hY.comp measurable_prodMk_right
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator_one (hYu hF)]
  congr 1
  refine lintegral_congr fun b => ?_
  simp only [discountWeight, zero_mul, neg_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  by_cases hb : unitSquareTimeChangeRegularized A u.toNNReal b ∈ F
  · rw [indicator_of_mem hb, indicator_of_mem (show b ∈ unitSquareTimeChangeRegularized A
      u.toNNReal ⁻¹' F from hb)]
    rfl
  · rw [indicator_of_notMem hb, indicator_of_notMem (show b ∉ unitSquareTimeChangeRegularized A
      u.toNNReal ⁻¹' F from hb)]

/-- `⟨1_E, R_c 1_F⟩_ν = ∫_0^∞ e^{-c u} ∫ 1_E(x) P_x(Y_u ∈ F) ν(dx) du`. -/
theorem lintegral_indicator_mul_clockResolvent_zero_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (ν : Measure ℂ) [SFinite ν] (c : ℝ) {E F : Set ℂ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    ∫⁻ x, E.indicator 1 x * clockResolvent A 0 c (F.indicator 1) x ∂ν =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(c * u))) *
        ∫⁻ x, E.indicator 1 x * reflectedPlanarBrownianMotion 0 1 x
          (unitSquareTimeChangeRegularized A u.toNNReal ⁻¹' F) ∂ν := by
  have hY := measurable_timeChangeRegularized_uncurry hA
  have hk : Measurable fun p : ℂ × ℝ => reflectedPlanarBrownianMotion 0 1 p.1
      (unitSquareTimeChangeRegularized A p.2.toNNReal ⁻¹' F) := by
    have h := Measurable.lintegral_kernel_prod_right'
      (κ := (reflectedPlanarBrownianMotion 0 1).comap Prod.fst measurable_fst)
      (f := fun q : (ℂ × ℝ) × ContinuousPath ℂ =>
        F.indicator 1 (unitSquareTimeChangeRegularized A q.1.2.toNNReal q.2))
      ((measurable_one.indicator hF).comp
        (hY.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
    have heq : (fun p : ℂ × ℝ => reflectedPlanarBrownianMotion 0 1 p.1
        (unitSquareTimeChangeRegularized A p.2.toNNReal ⁻¹' F)) = fun p => ∫⁻ b,
          F.indicator 1 (unitSquareTimeChangeRegularized A p.2.toNNReal b)
            ∂(reflectedPlanarBrownianMotion 0 1 p.1) := by
      funext p
      rw [← lintegral_indicator_one (show MeasurableSet
        (unitSquareTimeChangeRegularized A p.2.toNNReal ⁻¹' F) from
          (hY.comp measurable_prodMk_right) hF)]
      refine lintegral_congr fun b => ?_
      by_cases hb : unitSquareTimeChangeRegularized A p.2.toNNReal b ∈ F
      · rw [indicator_of_mem hb, indicator_of_mem (show b ∈ (fun b =>
          unitSquareTimeChangeRegularized A p.2.toNNReal b) ⁻¹' F from hb)]
        rfl
      · rw [indicator_of_notMem hb, indicator_of_notMem (show b ∉ (fun b =>
          unitSquareTimeChangeRegularized A p.2.toNNReal b) ⁻¹' F from hb)]
    rw [heq]
    exact h
  have hu : ∀ x, Measurable fun u : ℝ => ENNReal.ofReal (Real.exp (-(c * u))) *
      reflectedPlanarBrownianMotion 0 1 x (unitSquareTimeChangeRegularized A u.toNNReal ⁻¹' F) :=
    fun x => (measurable_exp_neg_mul c).mul (hk.comp (measurable_const.prodMk measurable_id))
  calc ∫⁻ x, E.indicator 1 x * clockResolvent A 0 c (F.indicator 1) x ∂ν
      = ∫⁻ x, (∫⁻ u in Ioi (0 : ℝ), E.indicator 1 x * (ENNReal.ofReal (Real.exp (-(c * u))) *
          reflectedPlanarBrownianMotion 0 1 x
            (unitSquareTimeChangeRegularized A u.toNNReal ⁻¹' F))) ∂ν := by
        refine lintegral_congr fun x => ?_
        rw [clockResolvent_zero_indicator_eq hA c hF x, ← lintegral_const_mul _ (hu x)]
    _ = ∫⁻ u in Ioi (0 : ℝ), (∫⁻ x, E.indicator 1 x * (ENNReal.ofReal (Real.exp (-(c * u))) *
          reflectedPlanarBrownianMotion 0 1 x
            (unitSquareTimeChangeRegularized A u.toNNReal ⁻¹' F)) ∂ν) :=
        lintegral_lintegral_swap (by exact (((measurable_one.indicator hE).comp measurable_fst).mul
          (((measurable_exp_neg_mul c).comp measurable_snd).mul hk)).aemeasurable)
    _ = _ := by
        refine lintegral_congr fun u => ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun x => ?_
        ring

/-! ### Continuity of the integrated heat kernel -/

/-- Integrals of a continuous heat kernel over the second variable are jointly continuous. -/
theorem continuousOn_setIntegral_snd {p : ℝ → ℂ → ℂ → ℝ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1)) {S : Set ℝ} (hS : IsCompact S)
    (hS0 : S ⊆ Ioi 0) {F : Set ℂ} (hF : MeasurableSet F) :
    ContinuousOn (fun q : ℝ × ℂ => ∫ y in F ∩ closedSquare 0 1, p q.1 q.2 y ∂ν)
      (S ×ˢ closedSquare 0 1) := by
  have hK := isCompact_closedSquare (0 : ℂ) 1
  have hKm : MeasurableSet (closedSquare (0 : ℂ) 1) := hK.isClosed.measurableSet
  obtain ⟨M, hM⟩ := (hS.prod (hK.prod hK)).exists_bound_of_continuousOn
    (hpc.mono (prod_mono hS0 subset_rfl))
  refine continuousOn_of_dominated (bound := fun _ => M) (fun q hq => ?_) (fun q hq => ?_)
    (integrable_const M) ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ (hF.inter hKm)
    exact (hpc.comp (by fun_prop : Continuous fun y : ℂ => (q.1, q.2, y)).continuousOn
      fun y hy => ⟨hS0 hq.1, hq.2, hy⟩).mono inter_subset_right
  · filter_upwards [ae_restrict_mem (hF.inter hKm)] with y hy
    exact hM (q.1, q.2, y) ⟨hq.1, hq.2, hy.2⟩
  · filter_upwards [ae_restrict_mem (hF.inter hKm)] with y hy
    exact hpc.comp (by fun_prop : Continuous fun q : ℝ × ℂ => (q.1, q.2, y)).continuousOn
      fun q hq => ⟨hS0 hq.1, hq.2, hy.2⟩

/-- The integrated kernel `φ_{E,F}(u) = ∫_{E ∩ K₀} ∫_{F ∩ K₀} p(u, x, y) ν(dy) ν(dx)`. -/
noncomputable def integratedKernel (ν : Measure ℂ) (p : ℝ → ℂ → ℂ → ℝ) (E F : Set ℂ) (u : ℝ) : ℝ :=
  ∫ x in E ∩ closedSquare 0 1, ∫ y in F ∩ closedSquare 0 1, p u x y ∂ν ∂ν

section Kernel

variable {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {ν : Measure ℂ} [IsFiniteMeasure ν]
  {p : ℝ → ℂ → ℂ → ℝ}

/-- Rows integrated over a subset of `K₀` have mass at most one. -/
theorem setIntegral_inter_le_one
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1)) {t : ℝ} (ht : 0 < t) {x : ℂ}
    (hx : x ∈ closedSquare 0 1) {F : Set ℂ} (hF : MeasurableSet F) :
    0 ≤ ∫ y in F ∩ closedSquare 0 1, p t x y ∂ν ∧ ∫ y in F ∩ closedSquare 0 1, p t x y ∂ν ≤ 1 := by
  have hK := isCompact_closedSquare (0 : ℂ) 1
  have hKm : MeasurableSet (closedSquare (0 : ℂ) 1) := hK.isClosed.measurableSet
  have hc : ContinuousOn (fun y => p t x y) (closedSquare 0 1) :=
    hpc.comp (by fun_prop : Continuous fun y : ℂ => (t, x, y)).continuousOn
      fun y hy => ⟨ht, hx, hy⟩
  have hint : IntegrableOn (fun y => p t x y) (closedSquare 0 1) ν := hc.integrableOn_compact hK
  have h0 := (hp t ht x hx).1
  refine ⟨setIntegral_nonneg (hF.inter hKm) fun y hy => h0 y hy.2, ?_⟩
  exact (setIntegral_mono_set hint ((ae_restrict_mem hKm).mono fun y hy => h0 y hy)
    (inter_subset_right : F ∩ closedSquare 0 1 ⊆ closedSquare 0 1).eventuallyLE).trans_eq
      (hp.setIntegral_eq_one hνK hpc ht hx)

/-- `P_x(Y_u ∈ F) = ∫_{F ∩ K₀} p(u, x, y) ν(dy)`. -/
theorem reflected_preimage_eq_ofReal_setIntegral (hA : IsUnitSquarePCAF A)
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1)) {u : ℝ} (hu : 0 < u) {x : ℂ}
    (hx : x ∈ closedSquare 0 1) {F : Set ℂ} (hF : MeasurableSet F) :
    reflectedPlanarBrownianMotion 0 1 x (unitSquareTimeChangeRegularized A u.toNNReal ⁻¹' F) =
      ENNReal.ofReal (∫ y in F ∩ closedSquare 0 1, p u x y ∂ν) := by
  have hK := isCompact_closedSquare (0 : ℂ) 1
  have hKm : MeasurableSet (closedSquare (0 : ℂ) 1) := hK.isClosed.measurableSet
  have hc : ContinuousOn (fun y => p u x y) (closedSquare 0 1) :=
    hpc.comp (by fun_prop : Continuous fun y : ℂ => (u, x, y)).continuousOn
      fun y hy => ⟨hu, hx, hy⟩
  rw [IsLBMHeatKernel.reflected_regularized_preimage hA hp hx hu hF,
    ofReal_integral_eq_lintegral_ofReal ((hc.integrableOn_compact hK).mono_set inter_subset_right)
      ((ae_restrict_mem (hF.inter hKm)).mono fun y hy => (hp u hu x hx).1 y hy.2)]

/-- `∫ 1_E(x) P_x(Y_u ∈ F) ν(dx) = φ_{E,F}(u)`. -/
theorem lintegral_indicator_mul_preimage_eq (hA : IsUnitSquarePCAF A)
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1)) {u : ℝ} (hu : 0 < u) {E F : Set ℂ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    ∫⁻ x, E.indicator 1 x * reflectedPlanarBrownianMotion 0 1 x
      (unitSquareTimeChangeRegularized A u.toNNReal ⁻¹' F) ∂ν =
        ENNReal.ofReal (integratedKernel ν p E F u) := by
  have hK := isCompact_closedSquare (0 : ℂ) 1
  have hKm : MeasurableSet (closedSquare (0 : ℂ) 1) := hK.isClosed.measurableSet
  have hgc : ContinuousOn (fun x => ∫ y in F ∩ closedSquare 0 1, p u x y ∂ν) (closedSquare 0 1) :=
    (continuousOn_setIntegral_snd hpc (isCompact_singleton (x := u))
      (singleton_subset_iff.2 hu) hF).comp
        (by fun_prop : Continuous fun x : ℂ => (u, x)).continuousOn
        fun x hx => ⟨mem_singleton u, hx⟩
  have hKae : (E ∩ closedSquare 0 1 : Set ℂ) =ᵐ[ν] E :=
    inter_ae_eq_left_of_ae_eq_univ (ae_eq_univ.2 hνK)
  rw [← setLIntegral_eq_lintegral_indicator_one_mul hE, ← Measure.restrict_congr_set hKae,
    setLIntegral_congr_fun (hE.inter hKm) fun x hx =>
      reflected_preimage_eq_ofReal_setIntegral hA hp hpc hu hx.2 hF,
    ← ofReal_integral_eq_lintegral_ofReal ((hgc.integrableOn_compact hK).mono_set
      inter_subset_right) ((ae_restrict_mem (hE.inter hKm)).mono fun x hx =>
        (setIntegral_inter_le_one hp hνK hpc hu hx.2 hF).1)]
  rfl

/-- The integrated kernel is continuous on `(0, ∞)`. -/
theorem continuousOn_integratedKernel
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1)) {E F : Set ℂ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    ContinuousOn (integratedKernel ν p E F) (Ioi 0) := by
  have hKm : MeasurableSet (closedSquare (0 : ℂ) 1) :=
    (isCompact_closedSquare (0 : ℂ) 1).isClosed.measurableSet
  intro u₀ hu₀
  have h0 : 0 < u₀ := hu₀
  have hS0 : Icc (u₀ / 2) (2 * u₀) ⊆ Ioi 0 := fun u hu =>
    lt_of_lt_of_le (by linarith) hu.1
  have hg := continuousOn_setIntegral_snd (ν := ν) hpc isCompact_Icc hS0 hF
  have hon : ContinuousOn (integratedKernel ν p E F) (Icc (u₀ / 2) (2 * u₀)) := by
    show ContinuousOn (fun u => ∫ x in E ∩ closedSquare 0 1, ∫ y in F ∩ closedSquare 0 1,
      p u x y ∂ν ∂ν) _
    refine continuousOn_of_dominated (bound := fun _ => 1) (fun u hu => ?_) (fun u hu => ?_)
      (integrable_const 1) ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ (hE.inter hKm)
      exact (hg.comp (by fun_prop : Continuous fun x : ℂ => (u, x)).continuousOn
        fun x hx => ⟨hu, hx⟩).mono inter_subset_right
    · filter_upwards [ae_restrict_mem (hE.inter hKm)] with x hx
      obtain ⟨h1, h2⟩ := setIntegral_inter_le_one hp hνK hpc (hS0 hu) hx.2 hF
      rw [Real.norm_eq_abs, abs_of_nonneg h1]
      exact h2
    · filter_upwards [ae_restrict_mem (hE.inter hKm)] with x hx
      exact hg.comp (by fun_prop : Continuous fun u : ℝ => (u, x)).continuousOn
        fun u hu => ⟨hu, hx.2⟩
  exact (hon.continuousAt (Icc_mem_nhds (by linarith) (by linarith))).continuousWithinAt

theorem integratedKernel_nonneg
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1)) {E F : Set ℂ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) {u : ℝ} (hu : 0 < u) :
    0 ≤ integratedKernel ν p E F u ∧ integratedKernel ν p E F u ≤ (ν univ).toReal := by
  have hK := isCompact_closedSquare (0 : ℂ) 1
  have hKm : MeasurableSet (closedSquare (0 : ℂ) 1) := hK.isClosed.measurableSet
  have hgc : ContinuousOn (fun x => ∫ y in F ∩ closedSquare 0 1, p u x y ∂ν) (closedSquare 0 1) :=
    (continuousOn_setIntegral_snd hpc (isCompact_singleton (x := u))
      (singleton_subset_iff.2 hu) hF).comp
        (by fun_prop : Continuous fun x : ℂ => (u, x)).continuousOn
        fun x hx => ⟨mem_singleton u, hx⟩
  refine ⟨setIntegral_nonneg (hE.inter hKm) fun x hx =>
    (setIntegral_inter_le_one hp hνK hpc hu hx.2 hF).1, ?_⟩
  calc integratedKernel ν p E F u ≤ ∫ x in E ∩ closedSquare 0 1, (1 : ℝ) ∂ν :=
        setIntegral_mono_on ((hgc.integrableOn_compact hK).mono_set inter_subset_right)
          (integrable_const (1 : ℝ)) (hE.inter hKm) fun x hx =>
            (setIntegral_inter_le_one hp hνK hpc hu hx.2 hF).2
    _ = (ν (E ∩ closedSquare 0 1)).toReal := by
        rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real]
    _ ≤ (ν univ).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))

end Kernel

/-! ### Symmetry -/

/-- **The integrated kernel is symmetric**: `φ_{E,F} = φ_{F,E}` on `(0, ∞)`. -/
theorem integratedKernel_comm {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsUnitSquarePCAF A)
    [IsFiniteMeasure (unitSquareRevuzMeasure A)]
    (hνK : unitSquareRevuzMeasure A (closedSquare 0 1)ᶜ = 0)
    (hatom : ∀ y ∈ closedSquare 0 1, unitSquareRevuzMeasure A {y} = 0)
    {m A' β' : ℝ} (hm : 0 ≤ m) (hA' : 0 ≤ A') (hβ' : 0 < β')
    (hmass : unitSquareRevuzMeasure A univ ≤ ENNReal.ofReal m)
    (hball : ∀ y ∈ closedSquare 0 1, ∀ ρ : ℝ, 0 < ρ →
      unitSquareRevuzMeasure A (closedBall y ρ) ≤ ENNReal.ofReal (A' * ρ ^ β'))
    {p : ℝ → ℂ → ℂ → ℝ}
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) (unitSquareRevuzMeasure A) p)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1)) {E F : Set ℂ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) {t : ℝ} (ht : 0 < t) :
    integratedKernel (unitSquareRevuzMeasure A) p E F t =
      integratedKernel (unitSquareRevuzMeasure A) p F E t := by
  set ν := unitSquareRevuzMeasure A with hν
  have hU : ∀ z ∈ closedSquare 0 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun t => A t b) atTop atTop := fun z hz =>
    ae_tendsto_atTop_of_isLBMHeatKernel hA hp hz (hatom z hz)
  have hform : ∀ (E F : Set ℂ), MeasurableSet E → MeasurableSet F → ∀ c : ℝ,
      ∫⁻ x, E.indicator 1 x * clockResolvent A 0 c (F.indicator 1) x ∂ν =
        ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(c * u))) *
          ENNReal.ofReal (integratedKernel ν p E F u) := by
    intro E F hE hF c
    rw [lintegral_indicator_mul_clockResolvent_zero_eq hA.measurable ν c hE hF]
    exact setLIntegral_congr_fun measurableSet_Ioi fun u hu => by
      rw [lintegral_indicator_mul_preimage_eq hA hp hνK hpc hu hE hF]
  have h1 : ∀ x, F.indicator (1 : ℂ → ℝ≥0∞) x ≤ 1 := fun x => by
    by_cases hx : x ∈ F <;> simp [hx]
  refine eqOn_Ioi_of_laplace_eq (continuousOn_integratedKernel hp hνK hpc hE hF)
    (continuousOn_integratedKernel hp hνK hpc hF hE)
    (fun u hu => (integratedKernel_nonneg hp hνK hpc hE hF hu).1)
    (fun u hu => (integratedKernel_nonneg hp hνK hpc hF hE hu).1)
    (fun u hu => (integratedKernel_nonneg hp hνK hpc hE hF hu).2)
    (fun u hu => (integratedKernel_nonneg hp hνK hpc hF hE hu).2) (fun n => ?_) ht
  have h := lintegral_mul_clockResolvent_zero_comm hA hU hνK hatom hm hA' hβ' hmass hball
    (c := (n : ℝ) + 1) (by positivity) (measurable_one.indicator hF)
    (measurable_one.indicator hE) h1
  rw [hform E F hE hF, hform F E hF hE] at h
  exact h

/-- **Symmetry of the heat kernel of the time change**: `p(t, x, y) = p(t, y, x)` for `t > 0` and
`x, y ∈ K₀`. -/
theorem isLBMHeatKernel_symm {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsUnitSquarePCAF A)
    [IsFiniteMeasure (unitSquareRevuzMeasure A)]
    (hνK : unitSquareRevuzMeasure A (closedSquare 0 1)ᶜ = 0)
    (hatom : ∀ y ∈ closedSquare 0 1, unitSquareRevuzMeasure A {y} = 0)
    (hsupp : ∀ y ∈ closedSquare 0 1, ∀ r : ℝ, 0 < r →
      0 < unitSquareRevuzMeasure A (ball y r ∩ closedSquare 0 1))
    {m A' β' : ℝ} (hm : 0 ≤ m) (hA' : 0 ≤ A') (hβ' : 0 < β')
    (hmass : unitSquareRevuzMeasure A univ ≤ ENNReal.ofReal m)
    (hball : ∀ y ∈ closedSquare 0 1, ∀ ρ : ℝ, 0 < ρ →
      unitSquareRevuzMeasure A (closedBall y ρ) ≤ ENNReal.ofReal (A' * ρ ^ β'))
    {p : ℝ → ℂ → ℂ → ℝ}
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) (unitSquareRevuzMeasure A) p)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1)) {t : ℝ} (ht : 0 < t) {x : ℂ}
    (hx : x ∈ closedSquare 0 1) {y : ℂ} (hy : y ∈ closedSquare 0 1) :
    p t x y = p t y x := by
  set ν := unitSquareRevuzMeasure A with hν
  have hK := isCompact_closedSquare (0 : ℂ) 1
  have hKm : MeasurableSet (closedSquare (0 : ℂ) 1) := hK.isClosed.measurableSet
  have hpc' : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.2 s.2.1)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1) :=
    hpc.comp (by fun_prop : Continuous fun s : ℝ × ℂ × ℂ => (s.1, s.2.2, s.2.1)).continuousOn
      fun s hs => ⟨hs.1, hs.2.2, hs.2.1⟩
  have hcont2 : ContinuousOn (fun q : ℂ × ℂ => p t q.1 q.2)
      (closedSquare 0 1 ×ˢ closedSquare 0 1) :=
    hpc.comp (by fun_prop : Continuous fun q : ℂ × ℂ => (t, q.1, q.2)).continuousOn
      fun q hq => ⟨ht, hq.1, hq.2⟩
  have hint2 : IntegrableOn (fun q : ℂ × ℂ => p t q.1 q.2)
      (closedSquare 0 1 ×ˢ closedSquare 0 1) (ν.prod ν) :=
    hcont2.integrableOn_compact (hK.prod hK)
  -- rows integrated against sets
  have hrow : ∀ F : Set ℂ, MeasurableSet F → ∀ x ∈ closedSquare 0 1,
      ∫ y in F ∩ closedSquare 0 1, p t x y ∂ν = ∫ y in F ∩ closedSquare 0 1, p t y x ∂ν := by
    intro F hF
    have hc1 : ContinuousOn (fun x => ∫ y in F ∩ closedSquare 0 1, p t x y ∂ν)
        (closedSquare 0 1) :=
      (continuousOn_setIntegral_snd hpc (isCompact_singleton (x := t))
        (singleton_subset_iff.2 ht) hF).comp
          (by fun_prop : Continuous fun x : ℂ => (t, x)).continuousOn
          fun x hx => ⟨mem_singleton t, hx⟩
    have hc2 : ContinuousOn (fun x => ∫ y in F ∩ closedSquare 0 1, p t y x ∂ν)
        (closedSquare 0 1) :=
      (continuousOn_setIntegral_snd (p := fun s a b => p s b a) hpc' (isCompact_singleton (x := t))
        (singleton_subset_iff.2 ht) hF).comp
          (by fun_prop : Continuous fun x : ℂ => (t, x)).continuousOn
          fun x hx => ⟨mem_singleton t, hx⟩
    have h1 : ∀ x ∈ closedSquare 0 1, 0 ≤ ∫ y in F ∩ closedSquare 0 1, p t x y ∂ν :=
      fun x hx => setIntegral_nonneg (hF.inter hKm) fun y hy => (hp t ht x hx).1 y hy.2
    have h2 : ∀ x ∈ closedSquare 0 1, 0 ≤ ∫ y in F ∩ closedSquare 0 1, p t y x ∂ν :=
      fun x hx => setIntegral_nonneg (hF.inter hKm) fun y hy => (hp t ht y hy.2).1 x hx
    refine fun x hx => eqOn_of_forall_setLIntegral_eq hKm hsupp h1 h2 hc1 hc2
      (fun S hS => ?_) hx
    rw [← ofReal_integral_eq_lintegral_ofReal ((hc1.integrableOn_compact hK).mono_set
        inter_subset_right) ((ae_restrict_mem (hS.inter hKm)).mono fun x hx => h1 x hx.2),
      ← ofReal_integral_eq_lintegral_ofReal ((hc2.integrableOn_compact hK).mono_set
        inter_subset_right) ((ae_restrict_mem (hS.inter hKm)).mono fun x hx => h2 x hx.2)]
    congr 1
    have hsym := integratedKernel_comm hA hνK hatom hm hA' hβ' hmass hball hp hpc hS hF ht
    simp only [integratedKernel] at hsym
    rw [hsym]
    have hint : Integrable (Function.uncurry fun x y => p t x y)
        ((ν.restrict (F ∩ closedSquare 0 1)).prod (ν.restrict (S ∩ closedSquare 0 1))) := by
      rw [Measure.prod_restrict]
      exact hint2.mono_set (prod_mono inter_subset_right inter_subset_right)
    exact integral_integral_swap hint
  -- the kernel itself
  have hcol : ContinuousOn (fun y => p t x y) (closedSquare 0 1) :=
    hpc.comp (by fun_prop : Continuous fun y : ℂ => (t, x, y)).continuousOn
      fun y hy => ⟨ht, hx, hy⟩
  have hcol' : ContinuousOn (fun y => p t y x) (closedSquare 0 1) :=
    hpc.comp (by fun_prop : Continuous fun y : ℂ => (t, y, x)).continuousOn
      fun y hy => ⟨ht, hy, hx⟩
  refine eqOn_of_forall_setLIntegral_eq hKm hsupp (fun y hy => (hp t ht x hx).1 y hy)
    (fun y hy => (hp t ht y hy).1 x hx) hcol hcol' (fun S hS => ?_) hy
  rw [← ofReal_integral_eq_lintegral_ofReal ((hcol.integrableOn_compact hK).mono_set
      inter_subset_right) ((ae_restrict_mem (hS.inter hKm)).mono fun y hy =>
        (hp t ht x hx).1 y hy.2),
    ← ofReal_integral_eq_lintegral_ofReal ((hcol'.integrableOn_compact hK).mono_set
      inter_subset_right) ((ae_restrict_mem (hS.inter hKm)).mono fun y hy =>
        (hp t ht y hy.2).1 x hx),
    hrow S hS x hx]

end HarmonicBalls
