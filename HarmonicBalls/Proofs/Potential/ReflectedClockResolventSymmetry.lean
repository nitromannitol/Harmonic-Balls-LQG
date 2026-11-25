import HarmonicBalls.Proofs.Potential.ReflectedClockResolvent

/-!
# Symmetry of the resolvent of the time change

Let `A` be a clock of reflected Brownian motion in `K₀` (`IsUnitSquarePCAF A`), unbounded from
every start in `K₀`, with finite Revuz measure `ν` carried by `K₀`. For `β, c ≥ 0` let `G` and
`U` be the potential and the resolvent of `ReflectedClockResolvent.lean`.

* By the occupation identity from every start (`bind_pathOccupationMeasure_eq`), `G` has the
  kernel `g_β(x, y) = ∫_0^∞ e^{-β s} k_s(x, y) ds` with respect to `ν`
  (`clockGreen_eq_lintegral_squareGreenKernel`), symmetric since the Neumann kernel `k_s` is;
  so `⟨h, G f⟩_ν = ⟨f, G h⟩_ν` (`lintegral_mul_clockGreen_comm`).
* `U f ≤ G f`, so each `U(x, ·)` is absolutely continuous with respect to `ν`, and for bounded
  `h ≥ 0` the measure `∫ h(x) U(x, ·) ν(dx)` has a density `U* h` with respect to `ν`
  (`exists_clockResolvent_adjoint`): `⟨f, U* h⟩_ν = ⟨h, U f⟩_ν`.
* **Symmetry** (`lintegral_mul_clockResolvent_comm`): if `G 1` is bounded on `K₀`, then
  `⟨f, U h⟩_ν = ⟨h, U f⟩_ν` for measurable `0 ≤ f, h ≤ 1`. From the resolvent identity
  `U(I + c G) = G` and the symmetry of `G`: `(I + c G) U* h = G h` `ν`-a.e., hence
  `U G h = U (I + c G) U* h = G U* h`, and `U h + c U G h = G h = U* h + c G U* h` with
  `G h < ∞` gives `U h = U* h` `ν`-a.e. This is the argument of Fukushima–Oshima–Takeda,
  *Dirichlet forms and symmetric Markov processes*, 2nd ed. 2011, proof of Theorem 6.2.1, written
  for nonnegative functions.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

namespace HarmonicBalls

/-! ### The Green kernel -/

/-- The `β`-Green kernel of the square, `g_β(x, y) = ∫_0^∞ e^{-β s} k_s(x, y) ds`. -/
noncomputable def squareGreenKernel (β : ℝ) (x y : ℂ) : ℝ≥0∞ :=
  ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(β * s))) * squareNeumannKernel s.toNNReal x y

theorem measurable_squareGreenKernel (β : ℝ) :
    Measurable fun p : ℂ × ℂ => squareGreenKernel β p.1 p.2 := by
  have h : Measurable fun q : (ℂ × ℂ) × ℝ => ENNReal.ofReal (Real.exp (-(β * q.2))) *
      squareNeumannKernel q.2.toNNReal q.1.1 q.1.2 :=
    ((measurable_exp_neg_mul β).comp measurable_snd).mul
      (measurable_squareNeumannKernel_uncurry.comp
        ((measurable_real_toNNReal.comp measurable_snd).prodMk
          ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst))))
  exact h.lintegral_prod_right'

theorem squareGreenKernel_comm (β : ℝ) (x y : ℂ) :
    squareGreenKernel β x y = squareGreenKernel β y x := by
  unfold squareGreenKernel
  simp_rw [squareNeumannKernel_comm _ x y]

/-- **The kernel of the potential**: `G f(x) = ∫ g_β(x, y) f(y) ν(dy)` for `x ∈ K₀`. -/
theorem clockGreen_eq_lintegral_squareGreenKernel {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A)
    (hU : ∀ z ∈ closedSquare 0 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun t => A t b) atTop atTop) [IsFiniteMeasure (unitSquareRevuzMeasure A)]
    (hνK : unitSquareRevuzMeasure A (closedSquare 0 1)ᶜ = 0)
    {x : ℂ} (hx : x ∈ closedSquare 0 1) (β : ℝ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    clockGreen A β f x = ∫⁻ y, squareGreenKernel β x y * f y ∂unitSquareRevuzMeasure A := by
  have hκ : Measurable fun q : ℝ × ℂ => squareNeumannKernel q.1.toNNReal x q.2 :=
    measurable_squareNeumannKernel_uncurry.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd))
  have hdw := measurable_discountWeight β hf
  have h1 : clockGreen A β f x = ∫⁻ q, discountWeight β f q
      ∂((reflectedPlanarBrownianMotion 0 1 x).bind (pathOccupationMeasure A)) := by
    rw [Measure.lintegral_bind (measurable_pathOccupationMeasure hA.measurable).aemeasurable
      hdw.aemeasurable]
    refine lintegral_congr fun b => ?_
    rw [lintegral_pathOccupationMeasure hA.measurable hdw]
  rw [h1, bind_pathOccupationMeasure_eq hA hU hνK hx,
    lintegral_withDensity_eq_lintegral_mul _ hκ hdw, lintegral_prod_symm _ (hκ.mul hdw).aemeasurable]
  refine lintegral_congr fun y => ?_
  have hm : Measurable fun s : ℝ => ENNReal.ofReal (Real.exp (-(β * s))) *
      squareNeumannKernel s.toNNReal x y :=
    (measurable_exp_neg_mul β).mul (measurable_squareNeumannKernel_uncurry.comp
      (measurable_real_toNNReal.prodMk (measurable_const.prodMk measurable_const)))
  rw [squareGreenKernel, ← lintegral_mul_const _ hm]
  refine lintegral_congr fun s => ?_
  simp only [Pi.mul_apply, discountWeight]
  ring

/-- The Revuz measure carried by `K₀` charges almost only points of `K₀`. -/
theorem ae_mem_closedSquare_of_compl_eq_zero {ν : Measure ℂ}
    (hνK : ν (closedSquare 0 1)ᶜ = 0) : ∀ᵐ x ∂ν, x ∈ closedSquare 0 1 := by
  rw [ae_iff]
  exact hνK

/-- **Symmetry of the potential**: `⟨h, G f⟩_ν = ⟨f, G h⟩_ν`. -/
theorem lintegral_mul_clockGreen_comm {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A)
    (hU : ∀ z ∈ closedSquare 0 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun t => A t b) atTop atTop) [IsFiniteMeasure (unitSquareRevuzMeasure A)]
    (hνK : unitSquareRevuzMeasure A (closedSquare 0 1)ᶜ = 0) (β : ℝ) {h f : ℂ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f) :
    ∫⁻ x, h x * clockGreen A β f x ∂unitSquareRevuzMeasure A =
      ∫⁻ x, f x * clockGreen A β h x ∂unitSquareRevuzMeasure A := by
  have hK := ae_mem_closedSquare_of_compl_eq_zero hνK
  have hg := measurable_squareGreenKernel β
  have e1 : ∫⁻ x, h x * clockGreen A β f x ∂unitSquareRevuzMeasure A =
      ∫⁻ x, ∫⁻ y, h x * (squareGreenKernel β x y * f y) ∂unitSquareRevuzMeasure A
        ∂unitSquareRevuzMeasure A := by
    refine lintegral_congr_ae (hK.mono fun x hx => ?_)
    dsimp only
    rw [clockGreen_eq_lintegral_squareGreenKernel hA hU hνK hx β hf]
    exact (lintegral_const_mul _ ((hg.comp (measurable_const.prodMk measurable_id)).mul hf)).symm
  have e2 : ∫⁻ x, f x * clockGreen A β h x ∂unitSquareRevuzMeasure A =
      ∫⁻ x, ∫⁻ y, f x * (squareGreenKernel β x y * h y) ∂unitSquareRevuzMeasure A
        ∂unitSquareRevuzMeasure A := by
    refine lintegral_congr_ae (hK.mono fun x hx => ?_)
    dsimp only
    rw [clockGreen_eq_lintegral_squareGreenKernel hA hU hνK hx β hh]
    exact (lintegral_const_mul _ ((hg.comp (measurable_const.prodMk measurable_id)).mul hh)).symm
  rw [e1, e2, lintegral_lintegral_swap (by
    exact ((hh.comp measurable_fst).mul (hg.mul (hf.comp measurable_snd))).aemeasurable)]
  refine lintegral_congr fun x => lintegral_congr fun y => ?_
  rw [squareGreenKernel_comm β y x]
  ring

/-! ### The resolvent as a kernel -/

/-- The resolvent is dominated by the potential. -/
theorem resolventOccupation_le_clockOccupation (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (β : ℝ)
    {c : ℝ} (hc : 0 ≤ c) (f : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) :
    resolventOccupation A β c f b ≤ clockOccupation A (discountWeight β f) b := by
  unfold resolventOccupation clockOccupation
  refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
  exact mul_le_of_le_one_left zero_le (ENNReal.ofReal_le_one.2
    (Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hc (le_of_lt hu)))))

theorem clockResolvent_le_clockGreen (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (β : ℝ)
    {c : ℝ} (hc : 0 ≤ c) (f : ℂ → ℝ≥0∞) (x : ℂ) :
    clockResolvent A β c f x ≤ clockGreen A β f x :=
  lintegral_mono fun b => resolventOccupation_le_clockOccupation A β hc f b

/-- The occupation measure of the resolvent along a path. -/
noncomputable def resolventPathMeasure (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (β c : ℝ)
    (b : ContinuousPath ℂ) : Measure ℂ :=
  ((volume.restrict (Ioi (0 : ℝ))).withDensity fun u =>
    ENNReal.ofReal (Real.exp (-(c * u))) *
      ENNReal.ofReal (Real.exp (-(β *
        (pcafClockInverse (clockRationalRegularization A) u.toNNReal b : ℝ))))).map
    fun u => unitSquareTimeChangeRegularized A u.toNNReal b

theorem lintegral_resolventPathMeasure {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (β c : ℝ) {f : ℂ → ℝ≥0∞} (hf : Measurable f)
    (b : ContinuousPath ℂ) :
    ∫⁻ y, f y ∂resolventPathMeasure A β c b = resolventOccupation A β c f b := by
  have hφ := measurable_clockInverse_timeChange_uncurry hA
  have hY : Measurable fun u : ℝ => unitSquareTimeChangeRegularized A u.toNNReal b :=
    hφ.snd.comp measurable_prodMk_left
  have hw : Measurable fun u : ℝ => ENNReal.ofReal (Real.exp (-(c * u))) *
      ENNReal.ofReal (Real.exp (-(β *
        (pcafClockInverse (clockRationalRegularization A) u.toNNReal b : ℝ)))) :=
    (measurable_exp_neg_mul c).mul ((measurable_exp_neg_mul β).comp
      (hφ.fst.comp measurable_prodMk_left))
  rw [resolventPathMeasure, lintegral_map hf hY,
    lintegral_withDensity_eq_lintegral_mul _ hw (show Measurable fun u : ℝ =>
      f (unitSquareTimeChangeRegularized A u.toNNReal b) from hf.comp hY)]
  refine lintegral_congr fun u => ?_
  simp only [Pi.mul_apply, discountWeight]
  ring

theorem measurable_resolventPathMeasure {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (β c : ℝ) : Measurable (resolventPathMeasure A β c) := by
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  have h : (fun b => resolventPathMeasure A β c b S) = resolventOccupation A β c (S.indicator 1) := by
    funext b
    rw [← lintegral_indicator_one hS, lintegral_resolventPathMeasure hA β c
      (measurable_one.indicator hS)]
  rw [h]
  exact measurable_resolventOccupation hA β c (measurable_one.indicator hS)

/-- The resolvent measure `U(x, ·)`. -/
noncomputable def resolventMeasure (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (β c : ℝ) (x : ℂ) :
    Measure ℂ :=
  (reflectedPlanarBrownianMotion 0 1 x).bind (resolventPathMeasure A β c)

theorem lintegral_resolventMeasure {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (β c : ℝ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) (x : ℂ) :
    ∫⁻ y, f y ∂resolventMeasure A β c x = clockResolvent A β c f x := by
  rw [resolventMeasure, Measure.lintegral_bind (measurable_resolventPathMeasure hA β c).aemeasurable
    hf.aemeasurable]
  exact lintegral_congr fun b => lintegral_resolventPathMeasure hA β c hf b

theorem measurable_resolventMeasure {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (β c : ℝ) : Measurable (resolventMeasure A β c) := by
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  have h : (fun x => resolventMeasure A β c x S) = clockResolvent A β c (S.indicator 1) := by
    funext x
    rw [← lintegral_indicator_one hS, lintegral_resolventMeasure hA β c
      (measurable_one.indicator hS)]
  rw [h]
  exact measurable_clockResolvent hA β c (measurable_one.indicator hS)

/-- `U(x, ·) ≪ ν` for `x ∈ K₀`. -/
theorem resolventMeasure_absolutelyContinuous {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A)
    (hU : ∀ z ∈ closedSquare 0 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun t => A t b) atTop atTop) [IsFiniteMeasure (unitSquareRevuzMeasure A)]
    (hνK : unitSquareRevuzMeasure A (closedSquare 0 1)ᶜ = 0) (β : ℝ) {c : ℝ} (hc : 0 ≤ c)
    {x : ℂ} (hx : x ∈ closedSquare 0 1) :
    resolventMeasure A β c x ≪ unitSquareRevuzMeasure A := by
  refine Measure.AbsolutelyContinuous.mk fun N hN hνN => ?_
  rw [← lintegral_indicator_one hN, lintegral_resolventMeasure hA.measurable β c
    (measurable_one.indicator hN)]
  refine le_antisymm ((clockResolvent_le_clockGreen A β hc _ x).trans ?_) zero_le
  rw [clockGreen_eq_lintegral_squareGreenKernel hA hU hνK hx β (measurable_one.indicator hN)]
  refine (lintegral_congr_ae (g := fun _ => 0) ?_).trans lintegral_zero |>.le
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hνN] with y hy
  rw [indicator_of_notMem hy, mul_zero]

/-- A set integral as the integral of the indicator times the function. -/
theorem setLIntegral_eq_lintegral_indicator_one_mul {μ : Measure ℂ} {S : Set ℂ}
    (hS : MeasurableSet S) (F : ℂ → ℝ≥0∞) :
    ∫⁻ x in S, F x ∂μ = ∫⁻ x, S.indicator 1 x * F x ∂μ := by
  rw [← lintegral_indicator hS]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ S
  · rw [indicator_of_mem hx, indicator_of_mem hx, Pi.one_apply, one_mul]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]

/-- **The adjoint of the resolvent on bounded functions**: for measurable `0 ≤ h ≤ 1`, if `G 1`
is bounded on `K₀`, there is a measurable `U* h` with `⟨g, U* h⟩_ν = ⟨h, U g⟩_ν` for every
measurable `g ≥ 0`: the density of `∫ h(x) U(x, ·) ν(dx)` with respect to `ν`. -/
theorem exists_clockResolvent_adjoint {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A)
    (hU : ∀ z ∈ closedSquare 0 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun t => A t b) atTop atTop) [IsFiniteMeasure (unitSquareRevuzMeasure A)]
    (hνK : unitSquareRevuzMeasure A (closedSquare 0 1)ᶜ = 0) (β : ℝ) {c : ℝ} (hc : 0 ≤ c)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hG1 : ∀ x ∈ closedSquare 0 1, clockGreen A β (fun _ => 1) x ≤ C)
    {h : ℂ → ℝ≥0∞} (hh : Measurable h) (hh1 : ∀ x, h x ≤ 1) :
    ∃ φ : ℂ → ℝ≥0∞, Measurable φ ∧ ∀ g : ℂ → ℝ≥0∞, Measurable g →
      ∫⁻ x, g x * φ x ∂unitSquareRevuzMeasure A =
        ∫⁻ x, h x * clockResolvent A β c g x ∂unitSquareRevuzMeasure A := by
  set ν := unitSquareRevuzMeasure A with hν
  have hK := ae_mem_closedSquare_of_compl_eq_zero hνK
  set Θ := (ν.withDensity h).bind (resolventMeasure A β c) with hΘ_def
  have hΘ : ∀ g, Measurable g → ∫⁻ y, g y ∂Θ = ∫⁻ x, h x * clockResolvent A β c g x ∂ν := by
    intro g hg
    rw [hΘ_def, Measure.lintegral_bind (measurable_resolventMeasure hA.measurable β c).aemeasurable
      hg.aemeasurable]
    simp_rw [lintegral_resolventMeasure hA.measurable β c hg]
    rw [lintegral_withDensity_eq_lintegral_mul _ hh (measurable_clockResolvent hA.measurable β c hg)]
    rfl
  have hac : Θ ≪ ν := by
    refine Measure.AbsolutelyContinuous.mk fun N hN hνN => ?_
    rw [← lintegral_indicator_one hN, hΘ _ (measurable_one.indicator hN)]
    refine (lintegral_congr_ae (g := fun _ => 0) (hK.mono fun x hx => ?_)).trans lintegral_zero
    have h0 : resolventMeasure A β c x N = 0 :=
      resolventMeasure_absolutelyContinuous hA hU hνK β hc hx hνN
    rw [← lintegral_indicator_one hN, lintegral_resolventMeasure hA.measurable β c
      (measurable_one.indicator hN)] at h0
    rw [h0, mul_zero]
  have hfin : Θ univ ≠ ⊤ := by
    have h1 := hΘ (fun _ => 1) measurable_const
    rw [lintegral_one] at h1
    rw [h1]
    refine ne_top_of_le_ne_top (b := ∫⁻ _, C ∂ν) ?_ (lintegral_mono_ae (hK.mono fun x hx => ?_))
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top hC (measure_ne_top _ _)
    · exact (mul_le_mul' (hh1 x) ((clockResolvent_le_clockGreen A β hc _ x).trans
        (hG1 x hx))).trans_eq (one_mul C)
  have : IsFiniteMeasure Θ := ⟨lt_top_iff_ne_top.2 hfin⟩
  refine ⟨Θ.rnDeriv ν, Measure.measurable_rnDeriv _ _, fun g hg => ?_⟩
  have hw := Measure.withDensity_rnDeriv_eq Θ ν hac
  calc ∫⁻ x, g x * Θ.rnDeriv ν x ∂ν = ∫⁻ x, (Θ.rnDeriv ν * g) x ∂ν :=
        lintegral_congr fun x => mul_comm _ _
    _ = ∫⁻ x, g x ∂(ν.withDensity (Θ.rnDeriv ν)) :=
        (lintegral_withDensity_eq_lintegral_mul _ (Measure.measurable_rnDeriv _ _) hg).symm
    _ = ∫⁻ x, g x ∂Θ := by rw [hw]
    _ = ∫⁻ x, h x * clockResolvent A β c g x ∂ν := hΘ g hg

/-- **Symmetry of the resolvent of the time change** on bounded functions, if the potential of
`1` is bounded on `K₀`: `⟨f, U h⟩_ν = ⟨h, U f⟩_ν` for measurable `0 ≤ f, h ≤ 1`. -/
theorem lintegral_mul_clockResolvent_comm {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A)
    (hU : ∀ z ∈ closedSquare 0 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun t => A t b) atTop atTop) [IsFiniteMeasure (unitSquareRevuzMeasure A)]
    (hνK : unitSquareRevuzMeasure A (closedSquare 0 1)ᶜ = 0) (β : ℝ) {c : ℝ} (hc : 0 ≤ c)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hG1 : ∀ x ∈ closedSquare 0 1, clockGreen A β (fun _ => 1) x ≤ C)
    {h f : ℂ → ℝ≥0∞} (hh : Measurable h) (hf : Measurable f) (hh1 : ∀ x, h x ≤ 1) :
    ∫⁻ x, f x * clockResolvent A β c h x ∂unitSquareRevuzMeasure A =
      ∫⁻ x, h x * clockResolvent A β c f x ∂unitSquareRevuzMeasure A := by
  set ν := unitSquareRevuzMeasure A with hν
  have hK := ae_mem_closedSquare_of_compl_eq_zero hνK
  have hGm := fun {g : ℂ → ℝ≥0∞} (hg : Measurable g) => measurable_clockGreen hA.measurable β hg
  have hUm := fun {g : ℂ → ℝ≥0∞} (hg : Measurable g) => measurable_clockResolvent hA.measurable β c hg
  have hGle : ∀ x ∈ closedSquare 0 1, clockGreen A β h x ≤ C := by
    intro x hx
    refine le_trans (lintegral_mono fun b => ?_) (hG1 x hx)
    unfold clockOccupation
    exact lintegral_mono fun u => mul_le_mul' le_rfl (hh1 _)
  obtain ⟨φ, hφm, hφ⟩ := exists_clockResolvent_adjoint hA hU hνK β hc hC hG1 hh hh1
  -- the resolvent identity, `ν`-almost everywhere
  have hR : ∀ {g : ℂ → ℝ≥0∞}, Measurable g → ∀ᵐ x ∂ν, clockResolvent A β c g x +
      ENNReal.ofReal c * clockResolvent A β c (clockGreen A β g) x = clockGreen A β g x :=
    fun hg => hK.mono fun x hx => clockResolvent_add_clockResolvent_clockGreen hA hU β hc hg hx
  -- (a) `(I + c G) U* h = G h`
  have ha : ∀ᵐ x ∂ν, φ x + ENNReal.ofReal c * clockGreen A β φ x = clockGreen A β h x := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (hφm.add ((hGm hφm).const_mul _))
      (hGm hh) fun S hS _ => ?_
    have hg : Measurable (S.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hS
    rw [setLIntegral_eq_lintegral_indicator_one_mul hS, setLIntegral_eq_lintegral_indicator_one_mul hS]
    calc ∫⁻ x, S.indicator 1 x * (φ x + ENNReal.ofReal c * clockGreen A β φ x) ∂ν
        = ∫⁻ x, S.indicator 1 x * φ x ∂ν +
            ENNReal.ofReal c * ∫⁻ x, S.indicator 1 x * clockGreen A β φ x ∂ν := by
          simp_rw [mul_add]
          rw [lintegral_add_left (f := fun x => S.indicator 1 x * φ x) (hg.mul hφm),
            ← lintegral_const_mul (f := fun x => S.indicator 1 x * clockGreen A β φ x) _
              (hg.mul (hGm hφm))]
          congr 1
          refine lintegral_congr fun x => ?_
          ring
      _ = ∫⁻ x, h x * clockResolvent A β c (S.indicator 1) x ∂ν +
            ENNReal.ofReal c * ∫⁻ x, h x * clockResolvent A β c
              (clockGreen A β (S.indicator 1)) x ∂ν := by
          rw [hφ _ hg, lintegral_mul_clockGreen_comm hA hU hνK β hg hφm]
          congr 2
          rw [← hφ _ (hGm hg)]
          exact lintegral_congr fun x => mul_comm _ _
      _ = ∫⁻ x, h x * clockGreen A β (S.indicator 1) x ∂ν := by
          rw [← lintegral_const_mul (f := fun x => h x * clockResolvent A β c
              (clockGreen A β (S.indicator 1)) x) _ (hh.mul (hUm (hGm hg))),
            ← lintegral_add_left (f := fun x => h x * clockResolvent A β c (S.indicator 1) x)
              (hh.mul (hUm hg))]
          refine lintegral_congr_ae ((hR hg).mono fun x hx => ?_)
          dsimp only
          rw [← hx]
          ring
      _ = ∫⁻ x, S.indicator 1 x * clockGreen A β h x ∂ν :=
          lintegral_mul_clockGreen_comm hA hU hνK β hh hg
  -- (b) `U G h = G U* h` on `K₀`
  have hb : ∀ x ∈ closedSquare 0 1, clockResolvent A β c (clockGreen A β h) x =
      clockGreen A β φ x := by
    intro x hx
    have hac := resolventMeasure_absolutelyContinuous hA hU hνK β hc hx
    rw [← lintegral_resolventMeasure hA.measurable β c (hGm hh) x,
      lintegral_congr_ae (hac.ae_le (ha.mono fun y hy => hy.symm)),
      lintegral_add_left hφm, lintegral_const_mul _ (hGm hφm),
      lintegral_resolventMeasure hA.measurable β c hφm,
      lintegral_resolventMeasure hA.measurable β c (hGm hφm)]
    exact clockResolvent_add_clockResolvent_clockGreen hA hU β hc hφm hx
  -- (c) `U h = U* h`, `ν`-almost everywhere
  have hcanc : ∀ᵐ x ∂ν, clockResolvent A β c h x = φ x := by
    filter_upwards [hK, ha] with x hx hax
    have hR' := clockResolvent_add_clockResolvent_clockGreen hA hU β hc hh hx
    rw [hb x hx] at hR'
    have hfin : ENNReal.ofReal c * clockGreen A β φ x ≠ ⊤ :=
      ne_top_of_le_ne_top (ne_top_of_le_ne_top hC (hGle x hx)) (hax ▸ le_add_self)
    exact (ENNReal.add_left_inj hfin).1 (hR'.trans hax.symm)
  calc ∫⁻ x, f x * clockResolvent A β c h x ∂ν = ∫⁻ x, f x * φ x ∂ν :=
        lintegral_congr_ae (hcanc.mono fun x hx => by dsimp only; rw [hx])
    _ = ∫⁻ x, h x * clockResolvent A β c f x ∂ν := hφ f hf

end HarmonicBalls
