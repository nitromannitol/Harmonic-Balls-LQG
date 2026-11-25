import HarmonicBalls.Proofs.Potential.ReflectedGreenPotentialBound
import LatticeProb.Prob.OccupationMeasureKernel
import LatticeProb.Analysis.UniformLimitWeightedSetIntegrals

/-!
# The Revuz formula for clocks of reflected Brownian motion in the unit square

The Revuz measure `unitSquareRevuzMeasure A` of a clock `A` of reflected Brownian motion in the
unit square (FirstPass/Cited/Section2HeatKernel.lean) is an iterated `bind` computed on the
rational-time regularization `clockRationalRegularization A`. This module proves:

* the regularization is monotone in time and measurable in the path, and equals `A` along every
  path on which `A` is continuous and nondecreasing;
* the occupation kernel `b ↦ clockOccupationMeasure (regularized A · b) b` is measurable, so the
  Revuz measure is the genuine Revuz integral: `∫ g d(Rev A) = ∫_{K₀} dx E_x ∫_{(0,1]} g(b_s) dA_s`
  (`lintegral_unitSquareRevuzMeasure_of_isUnitSquarePCAF`);
* Lebesgue–Stieltjes integrals against continuous nondecreasing clocks converge when the clocks
  converge uniformly on `[0, 1]` (`tendsto_integral_clockOccupationMeasure_of_tendstoUniformlyOn`),
  and occupation integrals converge in measure when the clocks converge uniformly in probability
  (`tendstoInMeasure_integral_clockOccupationMeasure`);
* the Stieltjes measure of a clock `t ↦ ∫_0^t φ` with a continuous density `φ ≥ 0` is `φ ds`
  (`clockStieltjesFunction_measure_restrict_of_density`).

Credit: the proofs follow MatedCRT/FirstPass/Derived/RevuzRegularize.lean, RevuzKernel.lean,
RevuzFormula.lean, RevuzLintegral.lean, RevuzPositive.lean, StieltjesOccupationUniformLimit.lean,
OccupationIntegralInMeasure.lean and LQGApproxClockRevuz.lean of the IDLA-Mated-CRT
formalization, written there for planar Brownian motion and Lebesgue measure on the plane.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

/-! ### The rational-time regularization -/

/-- Every nonnegative real is bounded above by a nonnegative rational. -/
theorem exists_nnrat_gt_nnreal (t : ℝ≥0) : ∃ q : ℚ≥0, t < (q : ℝ≥0) := by
  obtain ⟨q, hq⟩ := exists_rat_gt (t : ℝ)
  have hq0 : 0 ≤ q := by
    have : (0 : ℝ) ≤ t := t.coe_nonneg
    exact_mod_cast this.trans hq.le
  refine ⟨⟨q, hq0⟩, ?_⟩
  exact_mod_cast hq

theorem exists_nnrat_btwn_nnreal {s t : ℝ≥0} (h : s < t) :
    ∃ q : ℚ≥0, s < (q : ℝ≥0) ∧ (q : ℝ≥0) < t := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (s : ℝ) < t from h)
  have hq0 : 0 ≤ q := by
    have : (0 : ℝ) ≤ s := s.coe_nonneg
    exact_mod_cast this.trans hq1.le
  exact ⟨⟨q, hq0⟩, by exact_mod_cast hq1, by exact_mod_cast hq2⟩

theorem nonempty_clockRationalRegularization_index (t : ℝ≥0) :
    Nonempty {q : ℚ≥0 // t < (q : ℝ≥0)} :=
  let ⟨q, hq⟩ := exists_nnrat_gt_nnreal t
  ⟨⟨q, hq⟩⟩

/-- For every path, the regularization is nondecreasing in time. -/
theorem clockRationalRegularization_monotone (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0)
    (b : ContinuousPath ℂ) : Monotone fun t => clockRationalRegularization A t b := by
  intro s t hst
  have hne := nonempty_clockRationalRegularization_index t
  unfold clockRationalRegularization
  split_ifs with h
  · refine le_ciInf fun q => ?_
    exact ciInf_le (OrderBot.bddBelow _) (⟨q.1, hst.trans_lt q.2⟩ : {q : ℚ≥0 // s < (q : ℝ≥0)})
  · exact le_rfl

/-- The regularization of measurable functionals is measurable in the path. -/
theorem measurable_clockRationalRegularization {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (t : ℝ≥0) : Measurable (clockRationalRegularization A t) := by
  classical
  unfold clockRationalRegularization
  refine Measurable.ite ?_ (Measurable.iInf fun q => hA _) measurable_const
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
    measurableSet_le (hA _) (hA _)

/-- Along a path on which `A` is continuous and nondecreasing, the regularization is `A`. -/
theorem clockRationalRegularization_eq_of_continuous_monotone {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    {b : ContinuousPath ℂ} (hc : Continuous fun t => A t b) (hm : Monotone fun t => A t b)
    (t : ℝ≥0) : clockRationalRegularization A t b = A t b := by
  have hne := nonempty_clockRationalRegularization_index t
  have hcond : ∀ p q : ℚ≥0, p ≤ q → A p b ≤ A q b := fun p q hpq => hm (by exact_mod_cast hpq)
  unfold clockRationalRegularization
  split_ifs
  refine le_antisymm ?_ (le_ciInf fun q => hm q.2.le)
  refine le_of_forall_gt_imp_ge_of_dense fun c hc' => ?_
  have hU : {s | A s b < c} ∈ 𝓝 t := hc.continuousAt.eventually (gt_mem_nhds hc')
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 (nhdsWithin_le_nhds hU)
  obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn_nnreal (show t < u from hu)
  exact (ciInf_le (OrderBot.bddBelow _) (⟨q, hq1⟩ : {q : ℚ≥0 // t < (q : ℝ≥0)})).trans
    (hsub ⟨hq1, hq2⟩).le

theorem clockOccupationMeasure_regularization_eq_of_path {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    {b : ContinuousPath ℂ} (hc : Continuous fun t => A t b) (hm : Monotone fun t => A t b) :
    clockOccupationMeasure (fun t => clockRationalRegularization A t b) b =
      clockOccupationMeasure (fun t => A t b) b := by
  have h : (fun t => clockRationalRegularization A t b) = fun t => A t b :=
    funext (clockRationalRegularization_eq_of_continuous_monotone hc hm)
  rw [h]

/-! ### Measurability of the occupation kernel -/

theorem clockStieltjesFunction_apply_of_monotone {a : ℝ≥0 → ℝ≥0} (h : Monotone a) (x : ℝ) :
    clockStieltjesFunction a x =
      Function.rightLim (fun y : ℝ => ((a y.toNNReal : ℝ≥0) : ℝ)) x := by
  unfold clockStieltjesFunction
  simp only [h, ↓reduceDIte]
  rfl

theorem measurable_clockStieltjesFunction_regularization {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (x : ℝ) :
    Measurable fun b : ContinuousPath ℂ =>
      clockStieltjesFunction (fun t => clockRationalRegularization A t b) x := by
  have hfun : (fun b : ContinuousPath ℂ =>
      clockStieltjesFunction (fun t => clockRationalRegularization A t b) x) =
      fun b => Function.rightLim
        (fun y : ℝ => ((clockRationalRegularization A y.toNNReal b : ℝ≥0) : ℝ)) x :=
    funext fun b => clockStieltjesFunction_apply_of_monotone
      (clockRationalRegularization_monotone A b) x
  rw [hfun]
  refine LatticeProb.measurable_rightLim_of_monotone
    (a := fun b y => ((clockRationalRegularization A y.toNNReal b : ℝ≥0) : ℝ))
    (fun b y z hyz => ?_)
    (fun y => measurable_coe_nnreal_real.comp (measurable_clockRationalRegularization hA _)) x
  exact_mod_cast clockRationalRegularization_monotone A b (Real.toNNReal_mono hyz)

/-- **The occupation kernel is measurable.** -/
theorem measurable_clockOccupationMeasure_regularization {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) :
    Measurable fun b : ContinuousPath ℂ =>
      clockOccupationMeasure (fun t => clockRationalRegularization A t b) b := by
  unfold clockOccupationMeasure
  exact LatticeProb.measurable_map_stieltjes_restrict_Ioc
    (F := fun b : ContinuousPath ℂ => clockStieltjesFunction (fun t => clockRationalRegularization A t b))
    (measurable_clockStieltjesFunction_regularization hA) (fun b s => b s.toNNReal)
    (fun b => b.continuous.comp continuous_real_toNNReal)
    (fun s => ContinuousMap.measurable_eval _)

/-! ### The Revuz formula -/

/-- `∫ g d(clockOccupationMeasure a b) = ∫_{(0,1]} g(b_s) da_s` for measurable `g ≥ 0`. -/
theorem lintegral_clockOccupationMeasure (a : ℝ≥0 → ℝ≥0) (b : ContinuousPath ℂ)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂clockOccupationMeasure a b =
      ∫⁻ s in Ioc (0 : ℝ) 1, g (b s.toNNReal) ∂(clockStieltjesFunction a).measure := by
  unfold clockOccupationMeasure
  exact lintegral_map hg (g := fun s : ℝ => b s.toNNReal)
    (b.continuous.comp continuous_real_toNNReal).measurable

/-- **The Revuz formula for nonnegative functions**, regularized form. -/
theorem lintegral_unitSquareRevuzMeasure {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂unitSquareRevuzMeasure A =
      ∫⁻ z in closedSquare 0 1, ∫⁻ b, ∫⁻ x, g x ∂clockOccupationMeasure
        (fun t => clockRationalRegularization A t b) b ∂(reflectedPlanarBrownianMotion 0 1 z) := by
  have hk := measurable_clockOccupationMeasure_regularization hA
  have hm : Measurable fun z : ℂ => (reflectedPlanarBrownianMotion 0 1 z).bind fun b =>
      clockOccupationMeasure (fun t => clockRationalRegularization A t b) b :=
    (Measure.measurable_bind' hk).comp (reflectedPlanarBrownianMotion 0 1).measurable
  unfold unitSquareRevuzMeasure
  rw [Measure.lintegral_bind hm.aemeasurable hg.aemeasurable]
  refine lintegral_congr fun z => ?_
  rw [Measure.lintegral_bind hk.aemeasurable hg.aemeasurable]

/-- **The Revuz formula for a positive continuous additive functional**:
`∫ g d(Rev A) = ∫_{K₀} dz E_z ∫_{(0,1]} g(b_s) dA_s`. -/
theorem lintegral_unitSquareRevuzMeasure_of_isUnitSquarePCAF {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂unitSquareRevuzMeasure A =
      ∫⁻ z in closedSquare 0 1, ∫⁻ b, ∫⁻ x, g x ∂clockOccupationMeasure (fun t => A t b) b
        ∂(reflectedPlanarBrownianMotion 0 1 z) := by
  rw [lintegral_unitSquareRevuzMeasure hA.measurable hg]
  refine setLIntegral_congr_fun (isCompact_closedSquare 0 1).isClosed.measurableSet
    fun z hz => lintegral_congr_ae ?_
  filter_upwards [hA.path z hz] with b hb
  rw [clockOccupationMeasure_regularization_eq_of_path hb.2.1 hb.2.2]

/-! ### Stieltjes measures of continuous clocks -/

/-- The Stieltjes function of a continuous nondecreasing clock is the clock itself. -/
theorem clockStieltjesFunction_apply_of_continuous {a : ℝ≥0 → ℝ≥0} (hm : Monotone a)
    (hc : Continuous a) (x : ℝ) : clockStieltjesFunction a x = (a x.toNNReal : ℝ) := by
  have hf : Monotone (fun x : ℝ => ((a x.toNNReal : ℝ≥0) : ℝ)) :=
    fun x y hxy => by exact_mod_cast hm (Real.toNNReal_mono hxy)
  have hcont : Continuous (fun x : ℝ => ((a x.toNNReal : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp (hc.comp continuous_real_toNNReal)
  unfold clockStieltjesFunction
  simp only [hm, ↓reduceDIte]
  rw [Monotone.stieltjesFunction_eq]
  exact hf.continuousWithinAt_Ioi_iff_rightLim_eq.1 hcont.continuousWithinAt

/-- The Stieltjes measure of an interval is the increment of a continuous nondecreasing clock. -/
theorem clockStieltjesFunction_measure_Ioc {a : ℝ≥0 → ℝ≥0} (hm : Monotone a) (hc : Continuous a)
    (x y : ℝ) : (clockStieltjesFunction a).measure (Ioc x y) =
      ENNReal.ofReal ((a y.toNNReal : ℝ) - a x.toNNReal) := by
  rw [StieltjesFunction.measure_Ioc, clockStieltjesFunction_apply_of_continuous hm hc,
    clockStieltjesFunction_apply_of_continuous hm hc]

theorem isFiniteMeasure_clockStieltjesFunction_restrict_Ioc {a : ℝ≥0 → ℝ≥0} (hm : Monotone a)
    (hc : Continuous a) (x y : ℝ) :
    IsFiniteMeasure (((clockStieltjesFunction a).measure).restrict (Ioc x y)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ, clockStieltjesFunction_measure_Ioc hm hc]
  exact ENNReal.ofReal_lt_top

theorem measureReal_clockStieltjesFunction_restrict_Ioc {a : ℝ≥0 → ℝ≥0} (hm : Monotone a)
    (hc : Continuous a) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (((clockStieltjesFunction a).measure).restrict (Ioc 0 1)).real (Ioc 0 t) =
      (a t.toNNReal : ℝ) - a 0 := by
  rw [measureReal_def, Measure.restrict_apply measurableSet_Ioc,
    inter_eq_left.2 (Ioc_subset_Ioc le_rfl ht.2), clockStieltjesFunction_measure_Ioc hm hc,
    Real.toNNReal_zero,
    ENNReal.toReal_ofReal (sub_nonneg.2 (NNReal.coe_le_coe.2 (hm (zero_le))))]

/-- **Uniform convergence of Lebesgue–Stieltjes integrals.** -/
theorem tendstoUniformlyOn_setIntegral_Ioc_clockStieltjesFunction {a : ℕ → ℝ≥0 → ℝ≥0}
    {a' : ℝ≥0 → ℝ≥0} (ham : ∀ k, Monotone (a k)) (hac : ∀ k, Continuous (a k))
    (hm : Monotone a') (hc : Continuous a')
    (hu : TendstoUniformlyOn (fun k t => (a k t : ℝ)) (fun t => (a' t : ℝ)) atTop (Icc 0 1))
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1)) :
    TendstoUniformlyOn (fun k t => ∫ s in Ioc 0 t, g s ∂(clockStieltjesFunction (a k)).measure)
      (fun t => ∫ s in Ioc 0 t, g s ∂(clockStieltjesFunction a').measure) atTop (Icc 0 1) := by
  have : ∀ k, IsFiniteMeasure (((clockStieltjesFunction (a k)).measure).restrict (Ioc 0 1)) :=
    fun k => isFiniteMeasure_clockStieltjesFunction_restrict_Ioc (ham k) (hac k) 0 1
  have : IsFiniteMeasure (((clockStieltjesFunction a').measure).restrict (Ioc 0 1)) :=
    isFiniteMeasure_clockStieltjesFunction_restrict_Ioc hm hc 0 1
  have hcdf : TendstoUniformlyOn
      (fun k t => (((clockStieltjesFunction (a k)).measure).restrict (Ioc 0 1)).real (Ioc 0 t))
      (fun t => (((clockStieltjesFunction a').measure).restrict (Ioc 0 1)).real (Ioc 0 t))
      atTop (Icc 0 1) := by
    rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
    intro ε hε
    filter_upwards [hu (ε / 2) (half_pos hε)] with k hk t ht
    have h0 : (0 : ℝ≥0) ∈ Icc (0 : ℝ≥0) 1 := ⟨le_rfl, zero_le_one⟩
    have h1 : t.toNNReal ∈ Icc (0 : ℝ≥0) 1 :=
      ⟨zero_le, by simpa using Real.toNNReal_le_toNNReal ht.2⟩
    have ht' := hk _ h1
    have h0' := hk _ h0
    rw [measureReal_clockStieltjesFunction_restrict_Ioc (ham k) (hac k) ht,
      measureReal_clockStieltjesFunction_restrict_Ioc hm hc ht]
    rw [Real.dist_eq] at ht' h0' ⊢
    calc |((a' t.toNNReal : ℝ) - a' 0) - ((a k t.toNNReal : ℝ) - a k 0)|
        = |((a' t.toNNReal : ℝ) - a k t.toNNReal) - ((a' 0 : ℝ) - a k 0)| := by congr 1; ring
      _ ≤ |(a' t.toNNReal : ℝ) - a k t.toNNReal| + |(a' 0 : ℝ) - a k 0| := abs_sub _ _
      _ < ε / 2 + ε / 2 := add_lt_add ht' h0'
      _ = ε := add_halves ε
  have key := LatticeProb.tendstoUniformlyOn_setIntegral_Ioc_of_measureReal hcdf hg
  have hrestr : ∀ (m : Measure ℝ) {t : ℝ}, t ∈ Icc (0 : ℝ) 1 →
      ∫ s in Ioc 0 t, g s ∂(m.restrict (Ioc 0 1)) = ∫ s in Ioc 0 t, g s ∂m := by
    intro m t ht
    rw [Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 (Ioc_subset_Ioc le_rfl ht.2)]
  exact (key.congr (Eventually.of_forall fun k t ht => hrestr _ ht)).congr_right
    (fun t ht => hrestr _ ht)

/-- The integral of a continuous function against the occupation measure of a path is the
Lebesgue–Stieltjes integral `∫_{(0,1]} f(b_s) da_s`. -/
theorem integral_clockOccupationMeasure {a : ℝ≥0 → ℝ≥0} (b : ContinuousPath ℂ) {f : ℂ → ℝ}
    (hf : Continuous f) :
    ∫ x, f x ∂clockOccupationMeasure a b =
      ∫ s in Ioc 0 1, f (b s.toNNReal) ∂(clockStieltjesFunction a).measure := by
  rw [clockOccupationMeasure]
  exact integral_map (φ := fun s : ℝ => b s.toNNReal)
    (b.continuous.comp continuous_real_toNNReal).measurable.aemeasurable hf.aestronglyMeasurable

/-- **Occupation integrals along a path converge under uniform convergence of the clocks.** -/
theorem tendsto_integral_clockOccupationMeasure_of_tendstoUniformlyOn {a : ℕ → ℝ≥0 → ℝ≥0}
    {a' : ℝ≥0 → ℝ≥0} (ham : ∀ k, Monotone (a k)) (hac : ∀ k, Continuous (a k))
    (hm : Monotone a') (hc : Continuous a')
    (hu : TendstoUniformlyOn (fun k t => (a k t : ℝ)) (fun t => (a' t : ℝ)) atTop (Icc 0 1))
    (b : ContinuousPath ℂ) {f : ℂ → ℝ} (hf : Continuous f) :
    Tendsto (fun k => ∫ x, f x ∂clockOccupationMeasure (a k) b) atTop
      (𝓝 (∫ x, f x ∂clockOccupationMeasure a' b)) := by
  simp only [integral_clockOccupationMeasure b hf]
  exact (tendstoUniformlyOn_setIntegral_Ioc_clockStieltjesFunction ham hac hm hc hu
    (hf.comp (b.continuous.comp continuous_real_toNNReal)).continuousOn).tendsto_at
    ⟨zero_le_one, le_rfl⟩

/-! ### Convergence in measure -/

/-- **Borel–Cantelli extraction.** -/
theorem exists_strictMono_ae_eventually_notMem {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {U : ℕ → ℝ → Set Ω} (hU : ∀ η : ℝ, 0 < η → Tendsto (fun k => μ (U k η)) atTop (𝓝 0))
    (hmono : ∀ k : ℕ, ∀ η η' : ℝ, 0 < η' → η' ≤ η → U k η ⊆ U k η')
    {ns : ℕ → ℕ} (hns : StrictMono ns) :
    ∃ ns' : ℕ → ℕ, StrictMono ns' ∧
      ∀ᵐ b ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop, b ∉ U (ns (ns' i)) η := by
  have hev : ∀ i : ℕ, ∀ᶠ j in atTop, μ (U (ns j) (1 / ((i : ℝ) + 1))) ≤ (1 / 2 : ℝ≥0∞) ^ i := by
    intro i
    have h0 := (hU (1 / ((i : ℝ) + 1)) (by positivity)).comp hns.tendsto_atTop
    have hpos : (0 : ℝ≥0∞) < (1 / 2 : ℝ≥0∞) ^ i := ENNReal.pow_pos (by simp) i
    exact (h0.eventually (gt_mem_nhds hpos)).mono fun j hj => hj.le
  obtain ⟨ns', hns', hle⟩ := Filter.extraction_forall_of_eventually hev
  refine ⟨ns', hns', ?_⟩
  have hsum : ∑' i : ℕ, μ (U (ns (ns' i)) (1 / ((i : ℝ) + 1))) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [ENNReal.tsum_geometric]
    simp
  filter_upwards [ae_eventually_notMem hsum] with b hb η hη
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hη
  filter_upwards [hb, eventually_ge_atTop N] with i hi hiN hmem
  refine hi (hmono _ _ _ (by positivity) ?_ hmem)
  have hNi : ((N : ℝ) + 1) ≤ (i : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hiN
  exact (one_div_le_one_div_of_le (by positivity) hNi).trans hN.le

/-- **Occupation integrals converge in measure** when the clocks converge uniformly on `[0, 1]`
in probability. -/
theorem tendstoInMeasure_integral_clockOccupationMeasure {μ : Measure (ContinuousPath ℂ)}
    [IsFiniteMeasure μ] {A : ℕ → ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ k, ∀ᵐ b ∂μ, Continuous (fun t => A k t b) ∧ Monotone (fun t => A k t b))
    (hG : ∀ᵐ b ∂μ, Continuous (fun t => G t b) ∧ Monotone (fun t => G t b))
    (hconv : ∀ η : ℝ, 0 < η → Tendsto
      (fun k => μ {b | ∃ t : ℝ≥0, t ≤ 1 ∧ η ≤ |(A k t b : ℝ) - (G t b : ℝ)|}) atTop (𝓝 0))
    {f : ℂ → ℝ} (hf : Continuous f)
    (hmeas : ∀ k, AEStronglyMeasurable
      (fun b => ∫ x, f x ∂clockOccupationMeasure (fun t => A k t b) b) μ) :
    TendstoInMeasure μ (fun k b => ∫ x, f x ∂clockOccupationMeasure (fun t => A k t b) b) atTop
      (fun b => ∫ x, f x ∂clockOccupationMeasure (fun t => G t b) b) := by
  rw [exists_seq_tendstoInMeasure_atTop_iff hmeas]
  intro ns hns
  obtain ⟨ns', hns', hae⟩ := exists_strictMono_ae_eventually_notMem μ
    (U := fun k η => {b | ∃ t : ℝ≥0, t ≤ 1 ∧ η ≤ |(A k t b : ℝ) - (G t b : ℝ)|}) hconv
    (fun k η η' hη' hle b ⟨t, ht, h⟩ => ⟨t, ht, hle.trans h⟩) hns
  refine ⟨ns', hns', ?_⟩
  have hAall : ∀ᵐ b ∂μ, ∀ k, Continuous (fun t => A k t b) ∧ Monotone (fun t => A k t b) :=
    ae_all_iff.2 hA
  filter_upwards [hae, hAall, hG] with b hb hAb hGb
  refine tendsto_integral_clockOccupationMeasure_of_tendstoUniformlyOn
    (a := fun i t => A (ns (ns' i)) t b) (a' := fun t => G t b)
    (fun i => (hAb _).2) (fun i => (hAb _).1) hGb.2 hGb.1 ?_ b hf
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  filter_upwards [hb η hη] with i hi t ht
  have ht1 : t ≤ 1 := ht.2
  rw [Real.dist_eq, abs_sub_comm]
  by_contra hcon
  exact hi ⟨t, ht1, not_lt.1 hcon⟩

/-- The occupation integral of a positive continuous additive functional against a continuous
`f ≥ 0` has a measurable version, the same for every start in the unit square. -/
theorem exists_measurable_version_integral_clockOccupationMeasure
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsUnitSquarePCAF A) {f : ℂ → ℝ} (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) :
    ∃ Φ : ContinuousPath ℂ → ℝ, Measurable Φ ∧ (∀ b, 0 ≤ Φ b) ∧ ∀ z ∈ closedSquare 0 1,
      (fun b => ∫ x, f x ∂clockOccupationMeasure (fun t => A t b) b)
        =ᵐ[reflectedPlanarBrownianMotion 0 1 z] Φ := by
  have hg : Measurable fun x => ENNReal.ofReal (f x) :=
    ENNReal.measurable_ofReal.comp hf.measurable
  have hΦ : Measurable fun b : ContinuousPath ℂ =>
      ∫⁻ y, ENNReal.ofReal (f y) ∂clockOccupationMeasure
        (fun u => clockRationalRegularization A u b) b :=
    (Measure.measurable_lintegral hg).comp
      (measurable_clockOccupationMeasure_regularization hA.measurable)
  refine ⟨_, hΦ.ennreal_toReal, fun b => ENNReal.toReal_nonneg, fun z hz => EventuallyEq.symm ?_⟩
  filter_upwards [hA.path z hz] with b hb
  show ENNReal.toReal _ = _
  rw [clockOccupationMeasure_regularization_eq_of_path hb.2.1 hb.2.2,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hf.aestronglyMeasurable]

/-! ### Clocks with a continuous density -/

/-- **The Stieltjes measure of a clock with a continuous density** `φ ≥ 0`, restricted to
`(0, 1]`, is `φ(s) ds`. -/
theorem clockStieltjesFunction_measure_restrict_of_density {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφ0 : ∀ s, 0 ≤ φ s) {c : ℝ≥0 → ℝ≥0} (hc : ∀ t : ℝ≥0, (c t : ℝ) = ∫ s in (0 : ℝ)..t, φ s) :
    ((clockStieltjesFunction c).measure).restrict (Ioc (0 : ℝ) 1) =
      ((volume : Measure ℝ).restrict (Ioc 0 1)).withDensity fun s => ENNReal.ofReal (φ s) := by
  have hint : ∀ u v : ℝ, IntervalIntegrable φ volume u v := fun u v => hφ.intervalIntegrable u v
  have hm : Monotone c := by
    intro s t hst
    rw [← NNReal.coe_le_coe, hc, hc, ← intervalIntegral.integral_add_adjacent_intervals
      (hint 0 s) (hint s t), le_add_iff_nonneg_right]
    exact intervalIntegral.integral_nonneg (by exact_mod_cast hst) fun u _ => hφ0 u
  have hcc : Continuous c := by
    refine continuous_induced_rng.2 ?_
    have h : Continuous fun t : ℝ => ∫ s in (0 : ℝ)..t, φ s :=
      intervalIntegral.continuous_primitive hint 0
    convert h.comp NNReal.continuous_coe using 1
    funext t
    exact hc t
  have hfull : (clockStieltjesFunction c).measure =
      ((volume : Measure ℝ).restrict (Ioi 0)).withDensity fun s => ENNReal.ofReal (φ s) := by
    refine Measure.ext_of_Ioc _ _ fun x y hxy => ?_
    rw [clockStieltjesFunction_measure_Ioc hm hcc, withDensity_apply _ measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc, Set.Ioc_inter_Ioi]
    rcases le_or_gt y 0 with hy | hy
    · have hx : x.toNNReal = 0 := Real.toNNReal_of_nonpos (hxy.le.trans hy)
      have hy' : y.toNNReal = 0 := Real.toNNReal_of_nonpos hy
      rw [hx, hy', sub_self, ENNReal.ofReal_zero,
        Set.Ioc_eq_empty (not_lt.2 (hy.trans le_sup_right)), Measure.restrict_empty,
        lintegral_zero_measure]
    · have hy' : ((y.toNNReal : ℝ≥0) : ℝ) = y := Real.coe_toNNReal _ hy.le
      have hxn : ((x.toNNReal : ℝ≥0) : ℝ) = max x 0 := Real.coe_toNNReal' x
      have hle : x ⊔ 0 ≤ y := sup_le hxy.le hy.le
      rw [← ofReal_integral_eq_lintegral_ofReal
        ((hφ.integrableOn_Icc (a := x ⊔ 0) (b := y)).mono_set Set.Ioc_subset_Icc_self)
        (ae_of_all _ hφ0), ← intervalIntegral.integral_of_le hle, hc, hc, hy', hxn]
      congr 1
      exact intervalIntegral.integral_interval_sub_left (hint 0 y) (hint 0 (x ⊔ 0))
  rw [hfull, restrict_withDensity measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_left.2 Set.Ioc_subset_Ioi_self]

/-- **The occupation integral of a clock with a continuous density `φ` along a path** is the
window integral `∫_{(0,1]} f(b_s) φ(s) ds`. -/
theorem integral_clockOccupationMeasure_of_density {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφ0 : ∀ s, 0 ≤ φ s) {c : ℝ≥0 → ℝ≥0} (hc : ∀ t : ℝ≥0, (c t : ℝ) = ∫ s in (0 : ℝ)..t, φ s)
    (b : ContinuousPath ℂ) {f : ℂ → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫ x, f x ∂clockOccupationMeasure c b =
      (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (f (b s.toNNReal)) * ENNReal.ofReal (φ s)).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hf.aestronglyMeasurable]
  congr 1
  have hev : Measurable fun s : ℝ => b s.toNNReal :=
    (b.continuous.comp continuous_real_toNNReal).measurable
  have hfm : Measurable fun x => ENNReal.ofReal (f x) :=
    ENNReal.measurable_ofReal.comp hf.measurable
  have hw := lintegral_withDensity_eq_lintegral_mul ((volume : Measure ℝ).restrict (Ioc 0 1))
    (f := fun s : ℝ => ENNReal.ofReal (φ s)) (ENNReal.measurable_ofReal.comp hφ.measurable)
    (g := fun s : ℝ => ENNReal.ofReal (f (b s.toNNReal))) (hfm.comp hev)
  unfold clockOccupationMeasure
  rw [lintegral_map hfm hev, clockStieltjesFunction_measure_restrict_of_density hφ hφ0 hc]
  refine hw.trans (setLIntegral_congr_fun measurableSet_Ioc fun s _ => ?_)
  simp only [Pi.mul_apply]
  exact mul_comm _ _

end HarmonicBalls
