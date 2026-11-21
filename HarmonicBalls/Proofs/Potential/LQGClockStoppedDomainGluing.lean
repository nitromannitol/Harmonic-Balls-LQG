import HarmonicBalls.Proofs.Potential.LQGClockBoundedAnnulusTests
import HarmonicBalls.Proofs.Potential.LQGClockAnnularExitUniformIntegrability
import HarmonicBalls.Proofs.Potential.LQGClockDyadicCellMomentUniform
import HarmonicBalls.Defs.LBM
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! # Exterior stopped clock occupations

Dyadic inserted-field occupations converge at countably many bounded stopped
horizons outside a fixed disc. The stopped clock splits at the closed half-disc
into two continuous, nonnegative and nondecreasing pieces.

Under a moment bound on the dyadic time cells of the bounded exterior
occupation, uniform in the smoothing scale, the exit-stopped exterior clocks
converge uniformly on the unit time interval almost surely under the
field-path product law, to a continuous, nonnegative and nondecreasing limit
(`ae_tendstoUniformlyOn_stopped_exterior_clock_of_cell_moment`).
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped NNReal ENNReal

namespace HarmonicBalls

private theorem exterior_occupation_eq_time (b : ContinuousPath ℂ) (T : ℝ≥0)
    (f : ℂ → ℝ) (hf : Measurable f) :
    (∫ z, f z ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
      (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic T)))) =
    ∫ s in (0 : ℝ)..(min (1 : ℝ≥0) T : ℝ), f (b s.toNNReal) := by
  rw [integral_map b.continuous.measurable.aemeasurable hf.aestronglyMeasurable]
  rw [Measure.restrict_map continuous_real_toNNReal.measurable measurableSet_Iic]
  rw [Measure.restrict_restrict (continuous_real_toNNReal.measurable measurableSet_Iic)]
  rw [integral_map (f := fun t : ℝ≥0 => f (b t)) continuous_real_toNNReal.measurable.aemeasurable
    (hf.comp b.continuous.measurable).aestronglyMeasurable]
  simp only [NNReal.coe_one]
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ min (1 : ℝ) (T : ℝ) from le_min zero_le_one T.coe_nonneg), ← integral_Icc_eq_integral_Ioc]
  congr 1
  congr 1
  ext s
  simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Icc, le_min_iff]
  constructor
  · rintro ⟨hs, h0, h1⟩
    exact ⟨h0, h1, (Real.toNNReal_le_iff_le_coe).mp hs⟩
  · rintro ⟨h0, h1, hT⟩
    exact ⟨(Real.toNNReal_le_iff_le_coe).mpr hT, h0, h1⟩

/-- The actual bounded exterior density has dyadic limits at any countable family of
path-dependent unit-time horizons. -/
theorem ae_brownian_field_tendsto_countable_bounded_exterior_clocks
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ)
    {R : ℝ} (hR : 0 < R) (T : ι → ContinuousPath ℂ → ℝ≥0) :
    ∀ᵐ b ∂planarBrownianMotion x, ∀ᵐ ω ∂P, ∀ i,
      ∃ L : ℝ, 0 ≤ L ∧ Tendsto (fun n : ℕ =>
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        ∫ s in (0 : ℝ)..(min (1 : ℝ≥0) (T i b) : ℝ),
          {z : ℂ | (1 : ℝ)/2 < ‖z‖ ∧ ‖z‖ ≤ R}.indicator (fun z =>
            ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) (b s.toNNReal))
        atTop (𝓝 L) := by
  let A : Set ℂ := {z | (1 : ℝ)/2 < ‖z‖ ∧ ‖z‖ ≤ R}
  let g : ℂ → ℝ := A.indicator (fun z => Real.exp (-γ*α*Real.log (max (1/2) ‖z‖)))
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  have hgm : Measurable g := by
    apply Measurable.indicator _ hA
    exact (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left (by norm_num)).ne')))).measurable
  let f : ℂ → ℝ := fun z => Real.exp (-γ*α*Real.log (max (1/2) ‖z‖))
  have hf : Continuous f := Real.continuous_exp.comp (continuous_const.mul
    ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left (by norm_num)).ne')))
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) R).bddAbove_image hf.continuousOn
  have hgK : ∀ z, |g z| ≤ max K 0 := by
    intro z
    by_cases hz : z ∈ A
    · have hzk : z ∈ Metric.closedBall (0 : ℂ) R := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
      have hk : f z ≤ K := hK ⟨z, hzk, rfl⟩
      rw [show g z = f z from Set.indicator_of_mem hz _, abs_of_pos (Real.exp_pos _)]
      exact hk.trans (le_max_left _ _)
    · rw [show g z = 0 from Set.indicator_of_notMem hz _, abs_zero]
      exact le_max_right _ _
  have hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ (R+1)-1/2 := by
    intro z hz
    have hzA : z ∈ A := by
      by_contra h
      exact hz (Set.indicator_of_notMem h _)
    linarith [hzA.2]
  have hs := ae_brownian_field_tendsto_countable_occupation_tests (ι := ι) hh hγ0 hγ2 x
    (R := R+1) (by linarith) hgm (le_max_right K 0) hgK hgs
  have hsmall : ∀ᶠ n : ℕ in atTop, (2 : ℝ)⁻¹ ^ (n+1) < 1/2 := by
    have ht : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ (n+1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_add_atTop_nat 1)
    exact ht.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [hs] with b hb
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let τ (i : ι) : ℝ≥0 := T i b
  let μ (i : ι) : Measure ℂ := Measure.map (fun t => b t) (ν.restrict (Iic (τ i)))
  have hμ (i : ι) : μ i ≤ Measure.map (fun t => b t) ν :=
    Measure.map_mono Measure.restrict_le_self b.continuous.measurable
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [hb μ hμ, ae_recentered_inserted_circle_average hh α, hHae] with ω hω hrec hH i
  obtain ⟨L, hL⟩ := hω i
  refine ⟨L, ?_, hL.congr' ?_⟩
  · apply isClosed_Ici.mem_of_tendsto hL
    filter_upwards with n
    simp only [Set.mem_Ici]
    apply integral_nonneg
    intro z
    apply mul_nonneg
    · exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
    · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
  · filter_upwards [hsmall] with n hn
    let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
    have he : 0 < ε := by dsimp [ε]; positivity
    have hc : Continuous (hcirc ω ε) := by
      rw [← funext (hH ε)]
      exact hHc ω ε he
    have heq : (fun z => g z * (ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0)))) =
        A.indicator (fun z => ε^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) := by
      funext z
      by_cases hz : z ∈ A
      · have hm : max ε ‖z‖ = ‖z‖ := max_eq_right (le_trans hn.le hz.1.le)
        have hm' : max (1/2 : ℝ) ‖z‖ = ‖z‖ := max_eq_right hz.1.le
        rw [show g z = f z from Set.indicator_of_mem hz _, Set.indicator_of_mem hz,
          ← hrec _ z he, hm]
        dsimp only [f]
        rw [hm']
        rw [show Real.exp (-γ * α * Real.log ‖z‖) *
          (ε ^ (γ ^ 2 / 2) * Real.exp (γ * (hcirc ω ε z - hcirc ω 1 0))) =
          ε ^ (γ ^ 2 / 2) * (Real.exp (-γ * α * Real.log ‖z‖) *
            Real.exp (γ * (hcirc ω ε z - hcirc ω 1 0))) by ring, ← Real.exp_add]
        congr 2
        ring
      · rw [show g z = 0 from Set.indicator_of_notMem hz _, Set.indicator_of_notMem hz, zero_mul]
    change (∫ z, g z * (ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0))) ∂(μ i)) =
      ∫ s in (0 : ℝ)..(min (1 : ℝ≥0) (τ i) : ℝ),
        A.indicator (fun z => ε^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) (b s.toNNReal)
    rw [heq]
    apply exterior_occupation_eq_time b (τ i)
    apply Measurable.indicator _ hA
    have hi : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z) := by
      have hr : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z) =
          fun z => hcirc ω ε z - hcirc ω 1 0 - α * Real.log (max ε ‖z‖) := by
        funext z
        exact (hrec ε z he).symm
      rw [hr]
      exact (hc.sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left he).ne')))
    exact (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hi))).measurable


/-- The actual exterior density has dyadic limits at any countable family of
unit-time horizons, including horizons stopped at the exit of a domain. -/
theorem ae_brownian_field_tendsto_countable_stopped_exterior_clocks
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ)
    {R : ℝ} (hR : 0 < R) (D : Set ℂ) (T : ι → ContinuousPath ℂ → ℝ≥0) :
    ∀ᵐ b ∂planarBrownianMotion x, ∀ᵐ ω ∂P, ∀ i,
      ∃ L : ℝ, 0 ≤ L ∧ Tendsto (fun n : ℕ =>
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        ∫ s in (0 : ℝ)..(min (1 : ℝ≥0)
          (min (T i b) (ContinuousPath.exitTime D b).toReal.toNNReal) : ℝ),
          {z : ℂ | (1 : ℝ)/2 < ‖z‖ ∧ ‖z‖ ≤ R}.indicator (fun z =>
            ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) (b s.toNNReal))
        atTop (𝓝 L) :=
  ae_brownian_field_tendsto_countable_bounded_exterior_clocks hh hγ0 hγ2 α x hR
    (fun i b => min (T i b) (ContinuousPath.exitTime D b).toReal.toNNReal)

/-- A continuous density splits at the closed half-disc, with both pieces
continuous in the same exit-stopped time variable. -/
theorem stopped_clock_halfDisc_exterior_split (f : ℂ → ℝ) (hf : Continuous f)
    (b : ContinuousPath ℂ) (D : Set ℂ) :
    let I : Set ℂ := {z | ‖z‖ ≤ (1 : ℝ)/2}
    let A : ℝ≥0 → ℝ := fun t => ∫ s in (0 : ℝ)..min (t : ℝ)
      (ContinuousPath.exitTime D b).toReal, I.indicator f (b s.toNNReal)
    let B : ℝ≥0 → ℝ := fun t => ∫ s in (0 : ℝ)..min (t : ℝ)
      (ContinuousPath.exitTime D b).toReal, Iᶜ.indicator f (b s.toNNReal)
    Continuous A ∧ Continuous B ∧ ∀ t : ℝ≥0,
      (∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
        f (b s.toNNReal)) = A t + B t := by
  let I : Set ℂ := {z | ‖z‖ ≤ (1 : ℝ)/2}
  let u : ℝ → ℝ := fun s => f (b s.toNNReal)
  let v : ℝ → ℝ := fun s => I.indicator f (b s.toNNReal)
  let w : ℝ → ℝ := fun s => Iᶜ.indicator f (b s.toNNReal)
  have hu : Continuous u := hf.comp (b.continuous.comp continuous_real_toNNReal)
  have hv (a c : ℝ) : IntervalIntegrable v volume a c := by
    simpa only [v, I, norm_nonneg, true_and] using
      intervalIntegrable_annular_density f hf 0 b a c
  have hw_eq : w = u - v := by
    funext s
    by_cases h : b s.toNNReal ∈ I
    · simp [w, u, v, h]
    · simp [w, u, v, h]
  have hw (a c : ℝ) : IntervalIntegrable w volume a c := by
    rw [hw_eq]
    exact (hu.intervalIntegrable a c).sub (hv a c)
  have hvcont := intervalIntegral.continuous_primitive (fun a c => hv a c) 0
  have hwcont := intervalIntegral.continuous_primitive (fun a c => hw a c) 0
  refine ⟨hvcont.comp (continuous_subtype_val.min continuous_const),
    hwcont.comp (continuous_subtype_val.min continuous_const), ?_⟩
  intro t
  have hsum : v + w = u := by
    rw [hw_eq]
    ext s
    simp [Pi.add_apply, Pi.sub_apply]
  rw [← intervalIntegral.integral_add (hv 0 _) (hw 0 _)]
  change (∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal, u s) =
    ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal, (v+w) s
  rw [hsum]


/-- A bounded spatial cutoff does not change the exterior occupation before exit. -/
theorem stopped_exterior_clock_eq_bounded (f : ℂ → ℝ) (b : ContinuousPath ℂ)
    (D : Set ℂ) (R : ℝ) (hD : ∀ z ∈ D, ‖z‖ ≤ R) (t : ℝ≥0) :
    (∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
      {z : ℂ | (1 : ℝ)/2 < ‖z‖}.indicator f (b s.toNNReal)) =
    ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
      {z : ℂ | (1 : ℝ)/2 < ‖z‖ ∧ ‖z‖ ≤ R}.indicator f (b s.toNNReal) := by
  refine intervalIntegral.integral_congr_ae ?_
  have hsingle : ∀ᵐ s : ℝ, s ≠ (ContinuousPath.exitTime D b).toReal := by
    rw [ae_iff]
    simpa only [Ne, not_not, Set.ofPred_eq_eq_singleton] using
      measure_singleton (ContinuousPath.exitTime D b).toReal
  filter_upwards [hsingle] with s hs hmem
  rw [Set.uIoc_of_le (le_min t.coe_nonneg ENNReal.toReal_nonneg)] at hmem
  have hslt : s < (ContinuousPath.exitTime D b).toReal :=
    lt_of_le_of_ne (hmem.2.trans (min_le_right _ _)) hs
  have hlt : s.toNNReal < (ContinuousPath.exitTime D b).toNNReal := by
    apply (Real.toNNReal_lt_iff_lt_coe hmem.1.le).mpr
    simpa only [ENNReal.coe_toNNReal_eq_toReal] using hslt
  have hbD : b s.toNNReal ∈ D := ContinuousPath.mem_of_lt_exitTime D b _
    (lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr hlt) ENNReal.coe_toNNReal_le_self)
  by_cases hb : (1 : ℝ)/2 < ‖b s.toNNReal‖
  · simp only [Set.indicator_of_mem, Set.mem_ofPred_eq, hb, hD _ hbD, and_self]
  · simp only [Set.indicator_of_notMem, Set.mem_ofPred_eq, hb, false_and, not_false_eq_true]

/-- The two stopped pieces of a nonnegative continuous density are nonnegative
and nondecreasing in time. -/
theorem stopped_clock_halfDisc_exterior_nonneg_monotone (f : ℂ → ℝ)
    (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) (b : ContinuousPath ℂ) (D : Set ℂ) :
    let I : Set ℂ := {z | ‖z‖ ≤ (1 : ℝ)/2}
    let A : ℝ≥0 → ℝ := fun t => ∫ s in (0 : ℝ)..min (t : ℝ)
      (ContinuousPath.exitTime D b).toReal, I.indicator f (b s.toNNReal)
    let B : ℝ≥0 → ℝ := fun t => ∫ s in (0 : ℝ)..min (t : ℝ)
      (ContinuousPath.exitTime D b).toReal, Iᶜ.indicator f (b s.toNNReal)
    (∀ t, 0 ≤ A t ∧ 0 ≤ B t) ∧ Monotone A ∧ Monotone B := by
  let I : Set ℂ := {z | ‖z‖ ≤ (1 : ℝ)/2}
  let u : ℝ → ℝ := fun s => f (b s.toNNReal)
  let v : ℝ → ℝ := fun s => I.indicator f (b s.toNNReal)
  let w : ℝ → ℝ := fun s => Iᶜ.indicator f (b s.toNNReal)
  have hu : Continuous u := hf.comp (b.continuous.comp continuous_real_toNNReal)
  have hv (a c : ℝ) : IntervalIntegrable v volume a c := by
    simpa only [v, I, norm_nonneg, true_and] using
      intervalIntegrable_annular_density f hf 0 b a c
  have hw_eq : w = u - v := by
    funext s
    by_cases h : b s.toNNReal ∈ I
    · simp [w, u, v, h]
    · simp [w, u, v, h]
  have hw (a c : ℝ) : IntervalIntegrable w volume a c := by
    rw [hw_eq]
    exact (hu.intervalIntegrable a c).sub (hv a c)
  have hv0 : ∀ s, 0 ≤ v s := fun s => Set.indicator_nonneg (fun z _ => hf0 z) _
  have hw0 : ∀ s, 0 ≤ w s := fun s => Set.indicator_nonneg (fun z _ => hf0 z) _
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact ⟨intervalIntegral.integral_nonneg_of_forall
      (le_min t.coe_nonneg ENNReal.toReal_nonneg) hv0,
      intervalIntegral.integral_nonneg_of_forall
      (le_min t.coe_nonneg ENNReal.toReal_nonneg) hw0⟩
  · intro s t hst
    exact intervalIntegral.integral_mono_interval le_rfl
      (le_min s.coe_nonneg ENNReal.toReal_nonneg) (min_le_min_right _ hst)
      (Eventually.of_forall hv0) (hv 0 _)
  · intro s t hst
    exact intervalIntegral.integral_mono_interval le_rfl
      (le_min s.coe_nonneg ENNReal.toReal_nonneg) (min_le_min_right _ hst)
      (Eventually.of_forall hw0) (hw 0 _)

/-- A continuous density restricted to a measurable set is interval integrable
along a continuous path. -/
theorem intervalIntegrable_indicator_along_path (f : ℂ → ℝ) (hf : Continuous f)
    {A : Set ℂ} (hA : MeasurableSet A) (b : ContinuousPath ℂ) (u v : ℝ) :
    IntervalIntegrable (fun s : ℝ => A.indicator f (b s.toNNReal)) volume u v := by
  have hc : Continuous fun s : ℝ => f (b s.toNNReal) :=
    hf.comp (b.continuous.comp continuous_real_toNNReal)
  refine (hc.intervalIntegrable u v).mono_fun ?_ (Eventually.of_forall fun s => ?_)
  · exact ((hf.measurable.indicator hA).comp
      (b.continuous.measurable.comp measurable_real_toNNReal)).aestronglyMeasurable
  · exact norm_indicator_le_norm_self f (b s.toNNReal)

/-- An increment of a stopped integral of a nonnegative function is bounded by
the unstopped integral over the same time cell. -/
theorem ofReal_stopped_integral_sub_le_lintegral {g : ℝ → ℝ} (hg0 : ∀ s, 0 ≤ g s)
    (hgi : ∀ u v : ℝ, IntervalIntegrable g volume u v) {u v τ : ℝ} (huv : u ≤ v) :
    ENNReal.ofReal ((∫ s in (0 : ℝ)..min v τ, g s) - ∫ s in (0 : ℝ)..min u τ, g s) ≤
      ∫⁻ s in Ioc u v, ENNReal.ofReal (g s) := by
  rw [intervalIntegral.integral_interval_sub_left (hgi 0 _) (hgi 0 _)]
  have hle : min u τ ≤ min v τ := min_le_min_right τ huv
  rw [intervalIntegral.integral_of_le hle,
    ofReal_integral_eq_lintegral_ofReal (hgi _ _).1 (Eventually.of_forall hg0)]
  apply lintegral_mono_set
  intro s hs
  refine ⟨?_, hs.2.trans (min_le_left _ _)⟩
  by_contra h
  have h1 : s ≤ min u τ := le_min (not_lt.mp h) (hs.2.trans (min_le_right _ _))
  exact absurd hs.1 (not_lt.mpr h1)

private theorem ae_continuous_stopped_exterior_density
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α : ℝ) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → Continuous (fun z => ε ^ (γ ^ 2 / 2) *
      Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hH hrec ε hε
  have hc : Continuous (hcirc ω ε) := by
    rw [← funext (hH ε)]
    exact hHc ω ε hε
  have hr : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z) =
      fun z => hcirc ω ε z - hcirc ω 1 0 - α * Real.log (max ε ‖z‖) := by
    funext z
    exact (hrec ε z hε).symm
  have hi : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z) := by
    rw [hr]
    exact (hc.sub continuous_const).sub (continuous_const.mul
      ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hε).ne')))
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hi))

/-- For a measurable set of the plane and a measurable nonnegative path functional `σ`,
the clock of the inserted density restricted to that set and stopped at time `σ` has a
version that is jointly measurable in the field, the path and the time, whose time paths
are continuous, nondecreasing and nonnegative, and which agrees with the clock off one
field-null set. -/
theorem exists_measurable_stopped_indicator_clock_prod_time
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {ε : ℝ} (hε : 0 < ε) (γ α : ℝ) {A : Set ℂ} (hA : MeasurableSet A)
    {σ : ContinuousPath ℂ → ℝ} (hσ : Measurable σ) (hσ0 : ∀ b, 0 ≤ σ b) :
    ∃ M : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable M ∧
      (∀ q, Continuous (fun t => M (q, t)) ∧ Monotone (fun t => M (q, t)) ∧
        ∀ t, 0 ≤ M (q, t)) ∧
      ∀ᵐ ω ∂P, ∀ (b : ContinuousPath ℂ) (t : ℝ≥0),
        M ((ω, b), t) = ∫ s in (0 : ℝ)..min (t : ℝ) (σ b),
          A.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) (b s.toNNReal) := by
  obtain ⟨H, hHc, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let f (ω : Ω) (z : ℂ) : ℝ := ε ^ (γ ^ 2 / 2) * Real.exp
    (γ * (H ω ε z - H ω 1 0 - α * Real.log (max ε ‖z‖)))
  have hf (ω : Ω) : Continuous (f ω) := by
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (((hHc ω ε hε).sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hε).ne'))))))
  have hf0 (ω : Ω) (z : ℂ) : 0 ≤ f ω z :=
    mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le
  let J : Ω × ℂ → ℝ := fun q => A.indicator (f q.1) q.2
  have h1 : Measurable (fun q : Ω × ℂ => H q.1 ε q.2) :=
    (hHm ε hε).comp measurable_swap
  have h2 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
    (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
  have hJ : Measurable J := by
    apply Measurable.indicator _ (hA.preimage measurable_snd)
    exact measurable_const.mul (measurable_const.mul ((h1.sub h2).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp
  let U : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ := fun q =>
    min (q.2 : ℝ) (σ q.1.2)
  have hU : Measurable U := measurable_subtype_coe.comp measurable_snd |>.min
    (hσ.comp (measurable_snd.comp measurable_fst))
  have heval : Measurable (fun q : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ =>
      q.1.1.2 q.2.toNNReal) := by
    exact (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk
        (measurable_snd.comp (measurable_fst.comp measurable_fst)))
  let S : Set (((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ) := {q | 0 < q.2 ∧ q.2 ≤ U q.1}
  have hS : MeasurableSet S := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (hU.comp measurable_fst))
  let Q : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ → ℝ := fun q =>
    S.indicator (fun q => J (q.1.1.1, q.1.1.2 q.2.toNNReal)) q
  have hQ : Measurable Q :=
    (hJ.comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk heval)).indicator hS
  let M : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ := fun q => ∫ s, Q (q, s)
  have hM : Measurable M := hQ.stronglyMeasurable.integral_prod_right'.measurable
  have hMeq (ω : Ω) (b : ContinuousPath ℂ) (t : ℝ≥0) :
      M ((ω, b), t) = ∫ s in (0 : ℝ)..min (t : ℝ) (σ b),
        A.indicator (f ω) (b s.toNNReal) := by
    have ht : (0 : ℝ) ≤ min (t : ℝ) (σ b) :=
      le_min t.property (hσ0 b)
    rw [intervalIntegral.integral_of_le ht, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with s
    simp only [Q, S, U, J, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Ioc]
  have hgi (q : Ω × ContinuousPath ℂ) (u v : ℝ) :
      IntervalIntegrable (fun s : ℝ => A.indicator (f q.1) (q.2 s.toNNReal)) volume u v :=
    intervalIntegrable_indicator_along_path (f q.1) (hf q.1) hA q.2 u v
  have hg0 (q : Ω × ContinuousPath ℂ) (s : ℝ) : 0 ≤ A.indicator (f q.1) (q.2 s.toNNReal) :=
    Set.indicator_nonneg (fun z _ => hf0 q.1 z) _
  refine ⟨M, hM, fun q => ⟨?_, ?_, ?_⟩, ?_⟩
  · have heq : (fun t => M (q, t)) = fun t : ℝ≥0 =>
        ∫ s in (0 : ℝ)..min (t : ℝ) (σ q.2),
          A.indicator (f q.1) (q.2 s.toNNReal) := funext (hMeq q.1 q.2)
    rw [heq]
    exact (intervalIntegral.continuous_primitive (fun u v => hgi q u v) 0).comp
      (continuous_subtype_val.min continuous_const)
  · intro s t hst
    change M (q, s) ≤ M (q, t)
    rw [show M (q, s) = _ from hMeq q.1 q.2 s, show M (q, t) = _ from hMeq q.1 q.2 t]
    exact intervalIntegral.integral_mono_interval le_rfl
      (le_min s.coe_nonneg (hσ0 q.2)) (min_le_min_right _ hst)
      (Eventually.of_forall (hg0 q)) (hgi q 0 _)
  · intro t
    rw [show M (q, t) = _ from hMeq q.1 q.2 t]
    exact intervalIntegral.integral_nonneg_of_forall
      (le_min t.coe_nonneg (hσ0 q.2)) (hg0 q)
  · filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec
    intro b t
    rw [hMeq]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    by_cases hz : b s.toNNReal ∈ A
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      simp only [f, hω ε (b s.toNNReal), hω 1 0, hrec ε (b s.toNNReal) hε]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]

/-- Conditional bounded exterior clock convergence. Fix a Brownian start `x` and a
measurable nonnegative path functional `σ`. Suppose that the dyadic time cells
`[j 2⁻ᵐ, (j + 1) 2⁻ᵐ]` of the unstopped inserted occupation of the bounded exterior
`{1/2 < ‖z‖ ≤ R}` have `p`-th moments at most `C (2⁻ᵐ) ^ a` with `a > 1`, uniformly
in the dyadic smoothing scale, under the field-path product law. Then almost
surely the bounded exterior clocks stopped at time `σ` converge uniformly on
`[0, 1]` to a continuous, nondecreasing and nonnegative limit. -/
theorem ae_tendstoUniformlyOn_bounded_exterior_clock_of_cell_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ)
    {σ : ContinuousPath ℂ → ℝ} (hσ : Measurable σ) (hσ0 : ∀ b, 0 ≤ σ b) {R : ℝ} (hR : 0 < R)
    {p a C : ℝ} (hp : 0 < p) (ha : 1 < a)
    (hmom : ∀ n m j : ℕ, j < 2 ^ m →
      ∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc ((j : ℝ) / 2 ^ m) ((j + 1) / 2 ^ m),
        ENNReal.ofReal ({z : ℂ | (1 : ℝ) / 2 < ‖z‖ ∧ ‖z‖ ≤ R}.indicator (fun z =>
          dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z))
          (q.2 s.toNNReal))) ^ p ∂(P.prod (planarBrownianMotion x)) ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ m)⁻¹ ^ a)) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), ∃ F : ℝ → ℝ,
      ContinuousOn F (Icc 0 1) ∧ MonotoneOn F (Icc 0 1) ∧ (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ F t) ∧
      TendstoUniformlyOn (fun n (t : ℝ) =>
        ∫ s in (0 : ℝ)..min t (σ q.2),
          {z : ℂ | (1 : ℝ) / 2 < ‖z‖ ∧ ‖z‖ ≤ R}.indicator (fun z =>
            dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z))
            (q.2 s.toNNReal)) F atTop (Icc 0 1) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let μ := P.prod (planarBrownianMotion x)
  let A : Set ℂ := {z : ℂ | (1 : ℝ) / 2 < ‖z‖ ∧ ‖z‖ ≤ R}
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let dens (ω : Ω) (n : ℕ) (z : ℂ) : ℝ := dyadicScale (n + 1) ^ (γ ^ 2 / 2) *
    Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (n + 1)) z)
  have hdens0 (ω : Ω) (n : ℕ) (z : ℂ) : 0 ≤ dens ω n z :=
    mul_nonneg (Real.rpow_nonneg (dyadicScale_pos (n + 1)).le _) (Real.exp_pos _).le
  choose M hMm hMr hMae using fun n : ℕ =>
    exists_measurable_stopped_indicator_clock_prod_time hh (dyadicScale_pos (n + 1)) γ α hA hσ hσ0
  let X : ℕ → Ω × ContinuousPath ℂ → ℝ → ℝ := fun n q t => M n (q, t.toNNReal)
  have hXm (n : ℕ) (t : ℝ) : Measurable fun q => X n q t :=
    (hMm n).comp (measurable_id.prodMk measurable_const)
  have hXmono (q : Ω × ContinuousPath ℂ) (n : ℕ) : MonotoneOn (X n q) (Icc 0 1) :=
    ((hMr n q).2.1.comp fun _ _ h => Real.toNNReal_le_toNNReal h).monotoneOn _
  have hXcont (q : Ω × ContinuousPath ℂ) (n : ℕ) : ContinuousOn (X n q) (Icc 0 1) :=
    ((hMr n q).1.comp continuous_real_toNNReal).continuousOn
  have hgood : ∀ᵐ ω ∂P, (∀ (n : ℕ) (b : ContinuousPath ℂ) (t : ℝ≥0), M n ((ω, b), t) =
      ∫ s in (0 : ℝ)..min (t : ℝ) (σ b),
        A.indicator (dens ω n) (b s.toNNReal)) ∧ ∀ n, Continuous (dens ω n) := by
    filter_upwards [ae_all_iff.mpr hMae, ae_continuous_stopped_exterior_density hh γ α]
      with ω h1 h2
    exact ⟨h1, fun n => h2 _ (dyadicScale_pos (n + 1))⟩
  have hgood' : ∀ᵐ q ∂μ, (∀ (n : ℕ) (b : ContinuousPath ℂ) (t : ℝ≥0), M n ((q.1, b), t) =
      ∫ s in (0 : ℝ)..min (t : ℝ) (σ b),
        A.indicator (dens q.1 n) (b s.toNNReal)) ∧ ∀ n, Continuous (dens q.1 n) :=
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hgood
  have hconv : ∀ᵐ q ∂μ, ∀ m j : ℕ, j ≤ 2 ^ m →
      ∃ L : ℝ, Tendsto (fun n => X n q (j / 2 ^ m)) atTop (𝓝 L) := by
    have he : {q : Ω × ContinuousPath ℂ | ∀ m j : ℕ, j ≤ 2 ^ m →
        ∃ L : ℝ, Tendsto (fun n => X n q (j / 2 ^ m)) atTop (𝓝 L)} =
        ⋂ m : ℕ, ⋂ j : ℕ, {q | j ≤ 2 ^ m →
          ∃ L : ℝ, Tendsto (fun n => X n q (j / 2 ^ m)) atTop (𝓝 L)} := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    have hset : MeasurableSet {q : Ω × ContinuousPath ℂ | ∀ m j : ℕ, j ≤ 2 ^ m →
        ∃ L : ℝ, Tendsto (fun n => X n q (j / 2 ^ m)) atTop (𝓝 L)} := by
      rw [he]
      exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun j =>
        (MeasurableSet.const _).imp
          (measurableSet_exists_tendsto fun n => hXm n _)
    refine (Measure.ae_prod_iff_ae_ae hset).2 ((Measure.ae_ae_comm hset).2 ?_)
    have h40 := ae_brownian_field_tendsto_countable_bounded_exterior_clocks (ι := ℕ × ℕ)
      hh hγ0 hγ2 α x hR (fun i b => min (((i.2 : ℝ) / 2 ^ i.1).toNNReal) (σ b).toNNReal)
    filter_upwards [h40] with b hb
    filter_upwards [hb, hgood] with ω hω hωg
    intro m j hj
    obtain ⟨L, -, hL⟩ := hω (m, j)
    have hT1 : ((j : ℝ) / 2 ^ m).toNNReal ≤ 1 := by
      rw [Real.toNNReal_le_one]
      exact div_le_one_of_le₀ (by exact_mod_cast hj) (by positivity)
    have hmin : ((min (1 : ℝ≥0) (min (((j : ℝ) / 2 ^ m).toNNReal)
        (σ b).toNNReal) : ℝ≥0) : ℝ) = min ((((j : ℝ) / 2 ^ m).toNNReal : ℝ≥0) : ℝ) (σ b) := by
      rw [min_eq_right ((min_le_left _ _).trans hT1), NNReal.coe_min,
        Real.coe_toNNReal _ (hσ0 b)]
    refine ⟨L, Tendsto.congr (fun n => ?_) hL⟩
    show (∫ s in (0 : ℝ)..((min (1 : ℝ≥0) (min (((j : ℝ) / 2 ^ m).toNNReal)
        (σ b).toNNReal) : ℝ≥0) : ℝ),
          A.indicator (dens ω n) (b s.toNNReal)) =
      M n ((ω, b), ((j : ℝ) / 2 ^ m).toNNReal)
    rw [hωg.1 n b, hmin]
  have hmom' : ∀ n m j : ℕ, j < 2 ^ m →
      ∫⁻ q, ENNReal.ofReal (X n q ((j + 1) / 2 ^ m) - X n q (j / 2 ^ m)) ^ p ∂μ ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ m)⁻¹ ^ a) := by
    intro n m j hj
    refine le_trans (lintegral_mono_ae ?_) (hmom n m j hj)
    filter_upwards [hgood'] with q hq
    have hu : (0 : ℝ) ≤ j / 2 ^ m := by positivity
    have huv : (j : ℝ) / 2 ^ m ≤ (j + 1) / 2 ^ m :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h1 : X n q ((j + 1) / 2 ^ m) =
        ∫ s in (0 : ℝ)..min ((j + 1) / 2 ^ m) (σ q.2),
          A.indicator (dens q.1 n) (q.2 s.toNNReal) := by
      have h := hq.1 n q.2 (((j : ℝ) + 1) / 2 ^ m).toNNReal
      rwa [Real.coe_toNNReal _ (hu.trans huv)] at h
    have h0 : X n q (j / 2 ^ m) =
        ∫ s in (0 : ℝ)..min (j / 2 ^ m) (σ q.2),
          A.indicator (dens q.1 n) (q.2 s.toNNReal) := by
      have h := hq.1 n q.2 ((j : ℝ) / 2 ^ m).toNNReal
      rwa [Real.coe_toNNReal _ hu] at h
    rw [h1, h0]
    refine ENNReal.rpow_le_rpow ?_ hp.le
    exact ofReal_stopped_integral_sub_le_lintegral
      (fun s => Set.indicator_nonneg (fun z _ => hdens0 q.1 n z) _)
      (fun u v => intervalIntegrable_indicator_along_path _ (hq.2 n) hA q.2 u v) huv
  have hmain := ae_exists_continuousOn_monotoneOn_limit_of_dyadic_cell_moment (μ := μ) X
    (Eventually.of_forall hXmono) (Eventually.of_forall hXcont) hXm hconv hp ha hmom'
  filter_upwards [hmain, hgood'] with q hF hq
  obtain ⟨F, hFc, hFm, hFu⟩ := hF
  have hEq (n : ℕ) : EqOn (X n q) (fun t =>
      ∫ s in (0 : ℝ)..min t (σ q.2), A.indicator (dens q.1 n) (q.2 s.toNNReal)) (Icc 0 1) := by
    intro t ht
    have h1 := hq.1 n q.2 t.toNNReal
    rw [Real.coe_toNNReal t ht.1] at h1
    exact h1
  refine ⟨F, hFc, hFm, fun t ht => ?_, hFu.congr (Eventually.of_forall hEq)⟩
  exact ge_of_tendsto' (hFu.tendsto_at ht) fun n => (hMr n q).2.2 t.toNNReal

/-- Conditional exterior clock convergence. Fix a bounded open domain `D` in the
disc of radius `R` and a Brownian start `x`. Suppose that the dyadic time cells
`[j 2⁻ᵐ, (j + 1) 2⁻ᵐ]` of the unstopped inserted occupation of the bounded exterior
`{1/2 < ‖z‖ ≤ R}` have `p`-th moments at most `C (2⁻ᵐ) ^ a` with `a > 1`, uniformly
in the dyadic smoothing scale, under the field-path product law. Then almost
surely the exterior clocks stopped at the exit of `D` converge uniformly on
`[0, 1]` to a continuous, nondecreasing and nonnegative limit. -/
theorem ae_tendstoUniformlyOn_stopped_exterior_clock_of_cell_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ)
    {D : Set ℂ} (hD : IsOpen D) {R : ℝ} (hR : 0 < R) (hDR : ∀ z ∈ D, ‖z‖ ≤ R)
    {p a C : ℝ} (hp : 0 < p) (ha : 1 < a)
    (hmom : ∀ n m j : ℕ, j < 2 ^ m →
      ∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc ((j : ℝ) / 2 ^ m) ((j + 1) / 2 ^ m),
        ENNReal.ofReal ({z : ℂ | (1 : ℝ) / 2 < ‖z‖ ∧ ‖z‖ ≤ R}.indicator (fun z =>
          dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z))
          (q.2 s.toNNReal))) ^ p ∂(P.prod (planarBrownianMotion x)) ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ m)⁻¹ ^ a)) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), ∃ F : ℝ → ℝ,
      ContinuousOn F (Icc 0 1) ∧ MonotoneOn F (Icc 0 1) ∧ (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ F t) ∧
      TendstoUniformlyOn (fun n (t : ℝ) =>
        ∫ s in (0 : ℝ)..min t (ContinuousPath.exitTime D q.2).toReal,
          {z : ℂ | (1 : ℝ) / 2 < ‖z‖}.indicator (fun z =>
            dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z))
            (q.2 s.toNNReal)) F atTop (Icc 0 1) := by
  filter_upwards [ae_tendstoUniformlyOn_bounded_exterior_clock_of_cell_moment hh hγ0 hγ2 α x
    (ContinuousPath.measurable_exitTime D hD).ennreal_toReal (fun _ => ENNReal.toReal_nonneg)
    hR hp ha hmom] with q hq
  obtain ⟨F, hFc, hFm, hF0, hF⟩ := hq
  refine ⟨F, hFc, hFm, hF0, hF.congr (Eventually.of_forall fun n t ht => ?_)⟩
  have h := stopped_exterior_clock_eq_bounded (fun z => dyadicScale (n + 1) ^ (γ ^ 2 / 2) *
    Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z))
    q.2 D R hDR t.toNNReal
  rw [Real.coe_toNNReal t ht.1] at h
  exact h.symm

/-- Conditional stopped-domain clock assembly. Suppose that the closed half-disc
clocks converge uniformly on `[0, 1]` almost surely under the field-path product
law, and that the dyadic time cells of the bounded exterior occupation satisfy
the moment bound of `ae_tendstoUniformlyOn_stopped_exterior_clock_of_cell_moment`.
Then almost surely the full inserted clocks stopped at the exit of `D` converge
uniformly on `[0, 1]` to a continuous, nondecreasing and nonnegative limit. -/
theorem ae_tendstoUniformlyOn_stopped_domain_clock_of_halfDisc_of_cell_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ)
    {D : Set ℂ} (hD : IsOpen D) {R : ℝ} (hR : 0 < R) (hDR : ∀ z ∈ D, ‖z‖ ≤ R)
    (hin : ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∃ F : Icc (0 : ℝ) 1 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        TendstoUniformly
          (fun i (t : Icc (0 : ℝ) 1) =>
            stoppedAnnularClock (fun z => (dyadicScale (i+1))^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (i+1)) z)) 0
                (fun _ => t.1.toNNReal) q.2) F atTop)
    {p a C : ℝ} (hp : 0 < p) (ha : 1 < a)
    (hmom : ∀ n m j : ℕ, j < 2 ^ m →
      ∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc ((j : ℝ) / 2 ^ m) ((j + 1) / 2 ^ m),
        ENNReal.ofReal ({z : ℂ | (1 : ℝ) / 2 < ‖z‖ ∧ ‖z‖ ≤ R}.indicator (fun z =>
          dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z))
          (q.2 s.toNNReal))) ^ p ∂(P.prod (planarBrownianMotion x)) ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ m)⁻¹ ^ a)) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), ∃ F : ℝ → ℝ,
      ContinuousOn F (Icc 0 1) ∧ MonotoneOn F (Icc 0 1) ∧ (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ F t) ∧
      TendstoUniformlyOn (fun n (t : ℝ) =>
        ∫ s in (0 : ℝ)..min t (ContinuousPath.exitTime D q.2).toReal,
          dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1))
              (q.2 s.toNNReal))) F atTop (Icc 0 1) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hcont := (Measure.quasiMeasurePreserving_fst (μ := P)
    (ν := planarBrownianMotion x)).ae (ae_continuous_stopped_exterior_density hh γ α)
  filter_upwards [hin, ae_tendstoUniformlyOn_stopped_exterior_clock_of_cell_moment hh hγ0 hγ2
    α x hD hR hDR hp ha hmom, hcont] with q hqin hqex hqc
  obtain ⟨Fi, hFic, hFi0, hFim, hFi⟩ := hqin
  obtain ⟨Fe, hFec, hFem, hFe0, hFe⟩ := hqex
  let dens (n : ℕ) (z : ℂ) : ℝ := dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z)
  have hdc (n : ℕ) : Continuous (dens n) := hqc _ (dyadicScale_pos (n + 1))
  have hτ0 : 0 ≤ (ContinuousPath.exitTime D q.2).toReal := ENNReal.toReal_nonneg
  let c : ℝ → Icc (0 : ℝ) 1 := fun t =>
    Set.projIcc 0 1 zero_le_one (min t (ContinuousPath.exitTime D q.2).toReal)
  have hcc : Continuous c := continuous_projIcc.comp (continuous_id.min continuous_const)
  have hcm : Monotone c := (Set.monotone_projIcc zero_le_one).comp
    fun _ _ h => min_le_min_right _ h
  have hI : MeasurableSet {z : ℂ | ‖z‖ ≤ (1 : ℝ) / 2} :=
    measurableSet_le measurable_norm measurable_const
  have hE : MeasurableSet {z : ℂ | (1 : ℝ) / 2 < ‖z‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hin_eq (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      stoppedAnnularClock (dens n) 0 (fun _ => (c t).1.toNNReal) q.2 =
        ∫ s in (0 : ℝ)..min t (ContinuousPath.exitTime D q.2).toReal,
          {z : ℂ | ‖z‖ ≤ (1 : ℝ) / 2}.indicator (dens n) (q.2 s.toNNReal) := by
    have hmem : min t (ContinuousPath.exitTime D q.2).toReal ∈ Icc (0 : ℝ) 1 :=
      ⟨le_min ht.1 hτ0, (min_le_left _ _).trans ht.2⟩
    have hct : (c t).1 = min t (ContinuousPath.exitTime D q.2).toReal := by
      rw [show c t = ⟨_, hmem⟩ from Set.projIcc_of_mem _ hmem]
    have hup : min ((1 : ℝ≥0) : ℝ) ((c t).1.toNNReal : ℝ) =
        min t (ContinuousPath.exitTime D q.2).toReal := by
      rw [NNReal.coe_one, hct, Real.coe_toNNReal _ hmem.1, min_eq_right hmem.2]
    rw [stoppedAnnularClock_eq_time_integral _ (hdc n).measurable]
    simp only [hup, norm_nonneg, true_and]
  have hsplit (n : ℕ) (u : ℝ) : (∫ s in (0 : ℝ)..u, dens n (q.2 s.toNNReal)) =
      (∫ s in (0 : ℝ)..u, {z : ℂ | ‖z‖ ≤ (1 : ℝ) / 2}.indicator (dens n) (q.2 s.toNNReal)) +
        ∫ s in (0 : ℝ)..u, {z : ℂ | (1 : ℝ) / 2 < ‖z‖}.indicator (dens n) (q.2 s.toNNReal) := by
    rw [← intervalIntegral.integral_add
      (intervalIntegrable_indicator_along_path _ (hdc n) hI q.2 0 u)
      (intervalIntegrable_indicator_along_path _ (hdc n) hE q.2 0 u)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    show dens n (q.2 s.toNNReal) =
      {z : ℂ | ‖z‖ ≤ (1 : ℝ) / 2}.indicator (dens n) (q.2 s.toNNReal) +
        {z : ℂ | (1 : ℝ) / 2 < ‖z‖}.indicator (dens n) (q.2 s.toNNReal)
    by_cases h : ‖q.2 s.toNNReal‖ ≤ (1 : ℝ) / 2
    · rw [Set.indicator_of_mem (show q.2 s.toNNReal ∈ {z : ℂ | ‖z‖ ≤ (1 : ℝ) / 2} from h),
        Set.indicator_of_notMem
          (show q.2 s.toNNReal ∉ {z : ℂ | (1 : ℝ) / 2 < ‖z‖} from not_lt.mpr h), add_zero]
    · rw [Set.indicator_of_notMem (show q.2 s.toNNReal ∉ {z : ℂ | ‖z‖ ≤ (1 : ℝ) / 2} from h),
        Set.indicator_of_mem
          (show q.2 s.toNNReal ∈ {z : ℂ | (1 : ℝ) / 2 < ‖z‖} from not_le.mp h), zero_add]
  have hsum := (hFi.comp c).tendstoUniformlyOn.add hFe
  refine ⟨Fi ∘ c + Fe, ((hFic.comp hcc).continuousOn).add hFec,
    MonotoneOn.add ((hFim.comp hcm).monotoneOn _) hFem,
    fun t ht => add_nonneg (hFi0 (c t)) (hFe0 t ht), hsum.congr (Eventually.of_forall ?_)⟩
  intro n t ht
  show stoppedAnnularClock (dens n) 0 (fun _ => (c t).1.toNNReal) q.2 +
      (∫ s in (0 : ℝ)..min t (ContinuousPath.exitTime D q.2).toReal,
        {z : ℂ | (1 : ℝ) / 2 < ‖z‖}.indicator (dens n) (q.2 s.toNNReal)) =
    ∫ s in (0 : ℝ)..min t (ContinuousPath.exitTime D q.2).toReal, dens n (q.2 s.toNNReal)
  rw [hin_eq n t ht, hsplit]

end HarmonicBalls
