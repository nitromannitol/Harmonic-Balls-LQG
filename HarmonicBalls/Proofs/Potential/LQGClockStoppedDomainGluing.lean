import HarmonicBalls.Proofs.Potential.LQGClockBoundedAnnulusTests
import HarmonicBalls.Proofs.Potential.LQGClockAnnularExitUniformIntegrability
import HarmonicBalls.Defs.LBM

/-! # Exterior stopped clock occupations

Dyadic inserted-field occupations converge at countably many bounded stopped
horizons outside a fixed disc.
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
  let τ (i : ι) : ℝ≥0 := min (T i b) (ContinuousPath.exitTime D b).toReal.toNNReal
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

end HarmonicBalls
