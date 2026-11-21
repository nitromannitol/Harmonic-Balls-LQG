import HarmonicBalls.Proofs.Potential.LQGClockHalfDiscAtInsertionPoint
import HarmonicBalls.Defs.LBM

/-! # LQG clocks of the inserted field from exterior limits

Almost sure locally uniform convergence of continuous clock approximations to a limit with
measurable time marginals implies convergence in probability, uniformly on finite time
intervals; sums of approximations converging in this sense converge to the sum of the
limits. The whole-plane clock approximations of the inserted field split into half-disc
and exterior parts. With an almost sure locally uniform exterior limit, the half-disc
results give an LQG clock of the inserted field for almost every field: at the insertion
point for every `α < Q`, and away from it for every insertion strength.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology Metric
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- Almost sure locally uniform convergence of continuous approximations to a limit with
measurable time marginals gives convergence in measure, uniformly on `[0, T]`. -/
theorem tendsto_measure_of_ae_eventually_uniform {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (A : ℕ → X → ℝ≥0 → ℝ)
    (hAc : ∀ j x, Continuous (A j x)) (hAm : ∀ j t, Measurable (fun x => A j x t))
    (F : X → ℝ≥0 → ℝ) (hFm : ∀ t, Measurable (fun x => F x t))
    (hlim : ∀ᵐ x ∂μ, ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t ≤ T,
      |A j x t - F x t| < η) (T : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun j => μ {x | ∃ t ≤ T, η ≤ |A j x t - F x t|}) atTop (𝓝 0) := by
  have hFc : ∀ᵐ x ∂μ, Continuous (F x) := by
    filter_upwards [hlim] with x hx
    apply TendstoLocallyUniformly.continuous (F := fun j => A j x) (p := atTop) _
      (Filter.Frequently.of_forall fun j => hAc j x)
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hε t
    refine ⟨Iic (t + 1), Iic_mem_nhds (lt_add_one t), ?_⟩
    filter_upwards [hx (t + 1) ε hε] with k hk y hy
    rw [Real.dist_eq, abs_sub_comm]
    exact hk y hy
  let g : ℕ → X → ℝ≥0∞ := fun j x => ⨆ r : ℚ,
    ENNReal.ofReal |A j x (min (Real.toNNReal r) T) - F x (min (Real.toNNReal r) T)|
  have hgm : ∀ j, Measurable (g j) := fun j =>
    Measurable.iSup fun r => (((hAm j _).sub (hFm _)).abs).ennreal_ofReal
  have hS : Tendsto (fun j => μ {x | ENNReal.ofReal η ≤ g j x}) atTop (𝓝 0) := by
    have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (μ := μ)
      (A := (∅ : Set X)) (L := atTop) (As := fun j => {x | ENNReal.ofReal η ≤ g j x})
      MeasurableSet.empty (fun j => measurableSet_le measurable_const (hgm j)) ?_
    · simpa using h
    filter_upwards [hlim] with x hx
    filter_upwards [hx T (η / 2) (half_pos hη)] with j hj
    refine ⟨fun hjS => ?_, fun h => (Set.notMem_empty x h).elim⟩
    have hg : g j x ≤ ENNReal.ofReal (η / 2) :=
      iSup_le fun r => ENNReal.ofReal_le_ofReal (hj _ (min_le_right _ _)).le
    have hc := (show ENNReal.ofReal η ≤ g j x from hjS).trans hg
    rw [ENNReal.ofReal_le_ofReal_iff (by linarith)] at hc
    linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hS (fun _ => zero_le)
    fun j => measure_mono_ae ?_
  filter_upwards [hFc] with x hxc
  rintro ⟨t, ht, hle⟩
  exact (ENNReal.ofReal_le_ofReal hle).trans
    (ofReal_abs_le_iSup_rat ((hAc j x).sub hxc) ht)

/-- Convergence in measure, uniformly on `[0, T]`, is preserved by sums. -/
theorem tendsto_measure_add_of_tendsto_measure {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (A₁ A₂ : ℕ → X → ℝ≥0 → ℝ) (F₁ F₂ : X → ℝ≥0 → ℝ) (T : ℝ≥0) {η : ℝ}
    (h₁ : Tendsto (fun j => μ {x | ∃ t ≤ T, η / 2 ≤ |A₁ j x t - F₁ x t|}) atTop (𝓝 0))
    (h₂ : Tendsto (fun j => μ {x | ∃ t ≤ T, η / 2 ≤ |A₂ j x t - F₂ x t|}) atTop (𝓝 0)) :
    Tendsto (fun j => μ {x | ∃ t ≤ T,
      η ≤ |(A₁ j x t + A₂ j x t) - (F₁ x t + F₂ x t)|}) atTop (𝓝 0) := by
  have hsum := h₁.add h₂
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun j => (measure_mono ?_).trans (measure_union_le _ _)
  rintro x ⟨t, ht, hle⟩
  by_contra hx
  simp only [mem_union, mem_ofPred_eq, not_or, not_exists, not_and, not_le] at hx
  have h1 := hx.1 t ht
  have h2 := hx.2 t ht
  have h3 : |(A₁ j x t + A₂ j x t) - (F₁ x t + F₂ x t)| ≤
      |A₁ j x t - F₁ x t| + |A₂ j x t - F₂ x t| := by
    rw [show (A₁ j x t + A₂ j x t) - (F₁ x t + F₂ x t) =
      (A₁ j x t - F₁ x t) + (A₂ j x t - F₂ x t) by ring]
    exact abs_add_le _ _
  linarith

/-- The whole-plane clock approximation splits into its half-disc and exterior parts. -/
theorem lqgClockApprox_eq_halfDisc_add_exterior {γ : ℝ} {hε : ℝ → ℂ → ℝ} {ε : ℝ}
    (hf : Continuous (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε z)))
    (b : ContinuousPath ℂ) (t : ℝ≥0) :
    lqgClockApprox γ hε ε b t =
      (∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε z)) (b s.toNNReal)) +
      ∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | 1/2 < ‖z‖}.indicator
        (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε z)) (b s.toNNReal) := by
  set f : ℂ → ℝ := fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε z) with hfdef
  let B : Set ℂ := {z | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  let E : Set ℂ := {z | 1/2 < ‖z‖}
  have hB : MeasurableSet B := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  have hE : MeasurableSet E := measurableSet_lt measurable_const measurable_norm
  have hpath : Continuous (fun s : ℝ => b s.toNNReal) :=
    b.continuous.comp continuous_real_toNNReal
  have hfi : IntervalIntegrable (fun s : ℝ => f (b s.toNNReal)) volume 0 t :=
    (hf.comp hpath).intervalIntegrable _ _
  have hBi : IntervalIntegrable (fun s : ℝ => B.indicator f (b s.toNNReal)) volume 0 t := by
    refine hfi.mono_fun ((hf.measurable.indicator hB).comp hpath.measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => ?_)
    by_cases hs : b s.toNNReal ∈ B
    · simp [Set.indicator_of_mem hs]
    · simp [Set.indicator_of_notMem hs]
  have hEi : IntervalIntegrable (fun s : ℝ => E.indicator f (b s.toNNReal)) volume 0 t := by
    refine hfi.mono_fun ((hf.measurable.indicator hE).comp hpath.measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => ?_)
    by_cases hs : b s.toNNReal ∈ E
    · simp [Set.indicator_of_mem hs]
    · simp [Set.indicator_of_notMem hs]
  change (∫ s in (0 : ℝ)..(t : ℝ), f (b s.toNNReal)) = _
  rw [← intervalIntegral.integral_add hBi hEi]
  congr 1
  funext s
  by_cases h : ‖b s.toNNReal‖ ≤ 1/2
  · have hb : b s.toNNReal ∈ B := ⟨norm_nonneg _, h⟩
    have he : b s.toNNReal ∉ E := fun he => (not_lt.mpr h) he
    rw [Set.indicator_of_mem hb, Set.indicator_of_notMem he, add_zero]
  · have hb : b s.toNNReal ∉ B := fun hb => h hb.2
    have he : b s.toNNReal ∈ E := lt_of_not_ge h
    rw [Set.indicator_of_notMem hb, Set.indicator_of_mem he, zero_add]

/-- Indicators of measurable sets keep continuous densities interval integrable along
continuous paths. -/
theorem intervalIntegrable_indicator_path {f : ℂ → ℝ} (hf : Continuous f) {S : Set ℂ}
    (hS : MeasurableSet S) (b : ContinuousPath ℂ) (a c : ℝ) :
    IntervalIntegrable (fun s : ℝ => S.indicator f (b s.toNNReal)) volume a c := by
  have hpath : Continuous (fun s : ℝ => b s.toNNReal) :=
    b.continuous.comp continuous_real_toNNReal
  refine ((hf.comp hpath).intervalIntegrable a c).mono_fun
    ((hf.measurable.indicator hS).comp hpath.measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => ?_)
  by_cases hs : b s.toNNReal ∈ S
  · simp [Set.indicator_of_mem hs]
  · simp [Set.indicator_of_notMem hs]

/-- For almost every field the dyadic densities of the inserted field are continuous. -/
theorem ae_continuous_inserted_density {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α : ℝ) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (fun z => (dyadicScale k) ^ (γ ^ 2 / 2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z)) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec k
  have hc : Continuous (hcirc ω (dyadicScale k)) := by
    rw [← funext (hω (dyadicScale k))]
    exact hHc ω (dyadicScale k) (dyadicScale_pos k)
  have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) =
      fun z => hcirc ω (dyadicScale k) z - hcirc ω 1 0 -
        α * Real.log (max (dyadicScale k) ‖z‖) := by
    funext z
    exact (hrec _ z (dyadicScale_pos k)).symm
  have hci : Continuous (fun z =>
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) := by
    rw [heq]
    exact (hc.sub continuous_const).sub (continuous_const.mul
      ((continuous_const.max continuous_norm).log
        (fun _ => (lt_max_of_lt_left (dyadicScale_pos k)).ne')))
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hci))

/-- Gluing at a fixed field sample: half-disc clocks converging in measure and exterior
clocks converging almost surely and locally uniformly give an LQG clock. -/
theorem isLQGClock_of_halfDisc_tendsto_measure_of_exterior {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    (hc : ∀ k : ℕ, Continuous (fun z => (dyadicScale k) ^ (γ ^ 2 / 2) *
      Real.exp (γ * hε (dyadicScale k) z)))
    (Fh Ge : ContinuousPath ℂ → ℝ≥0 → ℝ) (hGm : ∀ t, Measurable (fun b => Ge b t))
    (hF : ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → Tendsto (fun j => planarBrownianMotion x {b | ∃ t ≤ T,
      η ≤ |(∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        (dyadicScale (j+1)) ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale (j+1)) z))
          (b s.toNNReal)) - Fh b t|}) atTop (𝓝 0))
    (hG : ∀ᵐ b ∂planarBrownianMotion x, ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
      ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
        |(∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | 1/2 < ‖z‖}.indicator (fun z =>
          (dyadicScale (j+1)) ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale (j+1)) z))
            (b s.toNNReal)) - Ge b t| < η) :
    IsLQGClock planarBrownianMotion γ hε x (fun b t => Fh b t + Ge b t) := by
  intro T η hη
  have hE : MeasurableSet {z : ℂ | 1/2 < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hext := tendsto_measure_of_ae_eventually_uniform (μ := planarBrownianMotion x)
    (fun j b t => ∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | 1/2 < ‖z‖}.indicator (fun z =>
      (dyadicScale (j+1)) ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale (j+1)) z))
        (b s.toNNReal))
    (fun j b => (intervalIntegral.continuous_primitive
      (intervalIntegrable_indicator_path (hc (j+1)) hE b) 0).comp NNReal.continuous_coe)
    (fun j t => (SubMarkovKernelSemigroup.stronglyMeasurable_feynmanKacAdditiveFunctional
      ((hc (j+1)).measurable.indicator hE) t).measurable)
    Ge hGm hG T (half_pos hη)
  have hsum := tendsto_measure_add_of_tendsto_measure (μ := planarBrownianMotion x)
    _ _ Fh Ge T (hF T (η / 2) (half_pos hη)) hext
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  refine hsum.congr fun j => ?_
  congr 1
  ext b
  simp only [mem_ofPred_eq, lqgClockApprox_eq_halfDisc_add_exterior (hc (j + 1))]

/-- **Inserted clock at the insertion point.** For `γ ^ 2 < 2` and `α < Q`, an almost sure
locally uniform exterior limit under the joint law gives an LQG clock of the inserted field
for Brownian motion started at the insertion point, for almost every field. -/
theorem exists_ae_isLQGClock_fieldCircleAverage_at_origin_of_exterior
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ)
    (hγ2 : γ ^ 2 < 2) (hα : α < lqgQ γ)
    (hext : ∃ G : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable G ∧
      ∀ᵐ p ∂(P.prod (planarBrownianMotion 0)), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
        ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | 1/2 < ‖z‖}.indicator (fun z =>
            (dyadicScale (j+1)) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                (p.2 s.toNNReal)) - G (p,t)| < η) :
    ∃ F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ, ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) 0 (F ω) := by
  have : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨Fh, hFh⟩ := exists_ae_tendsto_measure_halfDiscClock_at_origin hh hγ hγ2 hα
  obtain ⟨G, hGm, hG⟩ := hext
  refine ⟨fun ω b t => Fh ω b t + G ((ω, b), t), ?_⟩
  filter_upwards [hFh, Measure.ae_ae_of_ae_prod hG, ae_continuous_inserted_density hh γ α]
    with ω hω hGω hc
  exact isLQGClock_of_halfDisc_tendsto_measure_of_exterior hc (Fh ω) (fun b t => G ((ω, b), t))
    (fun t => hGm.comp ((measurable_const.prodMk measurable_id).prodMk measurable_const))
    hω hGω

/-- **Inserted clock away from the insertion point.** For a start `x ≠ 0`, `γ ^ 2 < 2` and
every insertion strength `α`, an almost sure locally uniform exterior limit under the joint
law gives an LQG clock of the inserted field for almost every field. -/
theorem exists_ae_isLQGClock_fieldCircleAverage_of_exterior_of_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {x : ℂ} (hx : x ≠ 0) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2) (α : ℝ)
    (hext : ∃ G : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable G ∧
      ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
        ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | 1/2 < ‖z‖}.indicator (fun z =>
            (dyadicScale (j+1)) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                (p.2 s.toNNReal)) - G (p,t)| < η) :
    ∃ F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ, ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) x (F ω) := by
  have : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨Fh, hFhm, -, hFh⟩ :=
    exists_measurable_locally_uniform_limit_halfDiscClock_of_ne_zero hh hx hγ hγ2 α
  obtain ⟨G, hGm, hG⟩ := hext
  refine ⟨fun ω b t => Fh ((ω, b), t) + G ((ω, b), t), ?_⟩
  have hB : MeasurableSet {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2} :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  filter_upwards [Measure.ae_ae_of_ae_prod hFh, Measure.ae_ae_of_ae_prod hG,
    ae_continuous_inserted_density hh γ α] with ω hFω hGω hc
  refine isLQGClock_of_halfDisc_tendsto_measure_of_exterior hc (fun b t => Fh ((ω, b), t))
    (fun b t => G ((ω, b), t))
    (fun t => hGm.comp ((measurable_const.prodMk measurable_id).prodMk measurable_const))
    (fun T η hη => ?_) hGω
  exact tendsto_measure_of_ae_eventually_uniform (μ := planarBrownianMotion x)
    (fun j b t => ∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator
      (fun z => (dyadicScale (j+1)) ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (j+1)) z)) (b s.toNNReal))
    (fun j b => (intervalIntegral.continuous_primitive
      (intervalIntegrable_indicator_path (hc (j+1)) hB b) 0).comp NNReal.continuous_coe)
    (fun j t => (SubMarkovKernelSemigroup.stronglyMeasurable_feynmanKacAdditiveFunctional
      ((hc (j+1)).measurable.indicator hB) t).measurable)
    (fun b t => Fh ((ω, b), t))
    (fun t => hFhm.comp ((measurable_const.prodMk measurable_id).prodMk measurable_const))
    hFω T hη

end HarmonicBalls
