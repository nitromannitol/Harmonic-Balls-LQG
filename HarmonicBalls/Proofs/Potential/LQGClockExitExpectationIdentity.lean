import HarmonicBalls.Proofs.Potential.LQGClockExitQuenchedUniformIntegrability
import HarmonicBalls.Proofs.Potential.LQGClockBoundedWeightStoppedIncrement
import HarmonicBalls.Proofs.Potential.LQGClockExitExpectationAssembly

/-! # The expected exit time of the inserted clock

Let `D` be a smooth bounded domain contained in the disc of radius `ρ ≥ 1`. Before the exit
time from `D`, the dyadic increment of the inserted clock density splits into its part in the
half disc `‖z‖ < 1/2` and a part in `1/2 ≤ ‖z‖ ≤ ρ`. On the latter region the inserted density
is the density normalized at radius `R = ρ + 1/2`, times the random constant
`exp (γ (h_R(0) - h_1(0)))` and a bounded weight. The integer-time decomposition of exit-time
integrals turns summable unit-horizon bounds, uniform over the start, into a finite expected sum
of the exit-time increments of each part: for the half-disc part this is an explicit hypothesis,
and for the other part it is the bounded-weight increment estimate. For almost every field the
random constant is finite, so the expected sum of the exit-time increments of the clock
approximations is finite, the approximations are uniformly integrable, and every LQG clock that
is almost surely a time-change clock has finite expected exit time, equal to the limit of the
expected Green integrals of the approximating measures. The half-disc hypothesis holds for every
`0 < γ < 2` when `α ≤ 0`, and when `0 < γ * α` and `γ ^ 2 / 2 < 2 - γ * α`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

private theorem exists_exterior_weight_bound (γ α ρ : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ,
      |({z : ℂ | 1/2 ≤ ‖z‖ ∧ ‖z‖ ≤ ρ}.indicator
        (fun z => Real.exp (-(γ * α) * Real.log (max (1/2) ‖z‖))) z)| ≤ M := by
  let f : ℂ → ℝ := fun z => Real.exp (-(γ * α) * Real.log (max (1/2) ‖z‖))
  have hf : Continuous f :=
    Real.continuous_exp.comp (continuous_const.mul
      ((continuous_const.max continuous_norm).log
        (fun _ => (lt_max_of_lt_left (by norm_num : (0 : ℝ) < 1/2)).ne')))
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) ρ).bddAbove_image hf.continuousOn
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro z
  by_cases hz : z ∈ {z : ℂ | 1/2 ≤ ‖z‖ ∧ ‖z‖ ≤ ρ}
  · have hzk : z ∈ Metric.closedBall (0 : ℂ) ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
    have hle : f z ≤ K := hK ⟨z, hzk, rfl⟩
    rw [Set.indicator_of_mem hz, abs_of_pos (Real.exp_pos _)]
    exact hle.trans (le_max_left K 0)
  · rw [Set.indicator_of_notMem hz, abs_zero]
    exact le_max_right K 0

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

set_option maxHeartbeats 400000 in
/-- The expected exit time of the inserted clock from half-disc increment bounds: summable
bounds on the expected increments of the half-disc part `‖z‖ < 1/2` of the dyadic clock
densities against sub-occupation measures of the unit-time Brownian occupation, uniform over the
start, make every LQG clock from a fixed start in a smooth bounded domain that is almost surely
a time-change clock have, for almost every field, finite expected LBM exit time equal to the
limit of the expected Green integrals of the approximating measures. -/
theorem ae_tendsto_clockApprox_green_expectedLBMExitTime_of_halfDisc_increments
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : Set ℂ} (hD : IsSmoothBoundedOpen D) {x : ℂ} (hx : x ∈ D)
    (cI : ℕ → ℝ≥0∞) (hcI : (∑' k, cI k) ≠ ⊤)
    (hI : ∀ (k : ℕ) (y : ℂ) (μ : ContinuousPath ℂ → Measure ℂ),
      (∀ b, μ b ≤ Measure.map (fun t => b t)
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) →
      (∫⁻ p, ENNReal.ofReal |(∫ z, {z : ℂ | ‖z‖ < 1/2}.indicator (fun z =>
          (dyadicScale (k+2)) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+2)) z)) z
            ∂(μ p.2)) -
        ∫ z, {z : ℂ | ‖z‖ < 1/2}.indicator (fun z =>
          (dyadicScale (k+1)) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+1)) z)) z
            ∂(μ p.2)| ∂(P.prod (planarBrownianMotion y))) ≤ cI k)
    (F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hclock : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) x (F ω))
    (hF : ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F ω b)) :
    ∀ᵐ ω ∂P, expectedLBMExitTime (F ω) D x ≠ ⊤ ∧
      Tendsto (fun k : ℕ => ∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) *
        ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) y)))
        atTop (𝓝 (expectedLBMExitTime (F ω) D x)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hDo : IsOpen D := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  have hDb : Bornology.IsBounded D := hD.1
  obtain ⟨r, hr⟩ := hDb.subset_ball (0 : ℂ)
  let ρ : ℝ := max r 1
  have hρ1 : 1 ≤ ρ := le_max_right _ _
  have hDρ : ∀ z ∈ D, ‖z‖ < ρ := fun z hz => by
    have := hr hz
    rw [Metric.mem_ball, dist_zero_right] at this
    exact lt_of_lt_of_le this (le_max_left _ _)
  let R : ℝ := ρ + 1/2
  have hR1 : 1 ≤ R := by simp only [R]; linarith
  have hR0 : 0 < R := by linarith
  let SE : Set ℂ := {z : ℂ | 1/2 ≤ ‖z‖ ∧ ‖z‖ ≤ ρ}
  have hSE : MeasurableSet SE := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let SI : Set ℂ := {z : ℂ | ‖z‖ < 1/2}
  have hSI : MeasurableSet SI := measurableSet_lt measurable_norm measurable_const
  let g : ℂ → ℝ := SE.indicator (fun z => Real.exp (-(γ * α) * Real.log (max (1/2) ‖z‖)))
  have hgm : Measurable g := by
    apply Measurable.indicator _ hSE
    exact (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_const.max continuous_norm).log
        (fun _ => (lt_max_of_lt_left (by norm_num : (0 : ℝ) < 1/2)).ne')))).measurable
  obtain ⟨M, hM, hgM⟩ := exists_exterior_weight_bound γ α ρ
  have hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ R - 1/2 := by
    intro z hz
    have hzE : z ∈ SE := by
      by_contra h
      exact hz (Set.indicator_of_notMem h _)
    simp only [R]
    linarith [hzE.2]
  obtain ⟨cE, hcE, hE⟩ :=
    exists_summable_uniform_bounded_weight_suboccupation_increment_bound hh hγ hγ2 hR1 hgm hM
      hgM hgs
  -- the jointly measurable version of the field
  obtain ⟨H, hHc, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let H' : Ω → ℝ → ℂ → ℝ := fun ω r z => H ω r z - H ω 1 0 - α * Real.log (max r ‖z‖)
  have hH1 : Measurable (fun p : Ω × ℂ => H p.1 1 0) :=
    (hHm 1 one_pos).comp ((measurable_const : Measurable fun _ : Ω × ℂ => (0 : ℂ)).prodMk
      measurable_fst)
  have hHR : Measurable (fun p : Ω × ℂ => H p.1 R 0) :=
    (hHm R hR0).comp ((measurable_const : Measurable fun _ : Ω × ℂ => (0 : ℂ)).prodMk
      measurable_fst)
  have hH'm (k : ℕ) : Measurable (fun p : Ω × ℂ => H' p.1 (dyadicScale k) p.2) := by
    have h1 : Measurable (fun p : Ω × ℂ => H p.1 (dyadicScale k) p.2) :=
      (hHm _ (dyadicScale_pos k)).comp measurable_swap
    have h3 : Measurable (fun p : Ω × ℂ => α * Real.log (max (dyadicScale k) ‖p.2‖)) :=
      measurable_const.mul (Real.measurable_log.comp
        (measurable_const.max (measurable_norm.comp measurable_snd)))
    exact (h1.sub hH1).sub h3
  have hH'c (k : ℕ) (ω : Ω) : Continuous (H' ω (dyadicScale k)) :=
    ((hHc ω _ (dyadicScale_pos k)).sub continuous_const).sub (continuous_const.mul
      ((continuous_const.max continuous_norm).log
        (fun _ => (lt_max_of_lt_left (dyadicScale_pos k)).ne')))
  have hae : ∀ᵐ ω ∂P, ∀ k : ℕ, H' ω (dyadicScale k) =
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hr k
    funext z
    simp only [H', hω]
    exact hr _ z (dyadicScale_pos k)
  -- densities
  let fH : ℕ → Ω × ℂ → ℝ := fun k p =>
    dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H' p.1 (dyadicScale k) p.2)
  have hfHm (k : ℕ) : Measurable (fH k) :=
    measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul (hH'm k)))
  have hfHc (k : ℕ) (ω : Ω) : Continuous (fun z => fH k (ω, z)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hH'c k ω)))
  let eR : ℕ → Ω × ℂ → ℝ := fun k p =>
    dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * (H p.1 (dyadicScale k) p.2 - H p.1 R 0))
  have heRm (k : ℕ) : Measurable (eR k) := by
    have h1 : Measurable (fun p : Ω × ℂ => H p.1 (dyadicScale k) p.2) :=
      (hHm _ (dyadicScale_pos k)).comp measurable_swap
    exact measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul (h1.sub hHR)))
  have heRc (k : ℕ) (ω : Ω) : Continuous (fun z => eR k (ω, z)) := by
    show Continuous (fun z => dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * (H ω (dyadicScale k) z - H ω R 0)))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      ((hHc ω _ (dyadicScale_pos k)).sub continuous_const)))
  let dI : ℕ → Ω × ℂ → ℝ := fun k =>
    (Prod.snd ⁻¹' SI).indicator (fun p => fH (k+2) p - fH (k+1) p)
  have hdIm (k : ℕ) : Measurable (dI k) :=
    ((hfHm (k+2)).sub (hfHm (k+1))).indicator (measurable_snd hSI)
  let dE : ℕ → Ω × ℂ → ℝ := fun k p => g p.2 * (eR (k+2) p - eR (k+1) p)
  have hdEm (k : ℕ) : Measurable (dE k) :=
    (hgm.comp measurable_snd).mul ((heRm (k+2)).sub (heRm (k+1)))
  let W : Ω → ℝ := fun ω => Real.exp (γ * (H ω R 0 - H ω 1 0))
  have hpath (b : ContinuousPath ℂ) : Continuous (fun s : ℝ => b s.toNNReal) :=
    b.continuous.comp continuous_real_toNNReal
  have hpathm (b : ContinuousPath ℂ) : Measurable (fun s : ℝ => b s.toNNReal) :=
    (hpath b).measurable
  have hdIi (k : ℕ) (ω : Ω) (b : ContinuousPath ℂ) (u v : ℝ) :
      IntervalIntegrable (fun s : ℝ => dI k (ω, b s.toNNReal)) volume u v := by
    have hc : Continuous (fun s : ℝ => fH (k+2) (ω, b s.toNNReal) - fH (k+1) (ω, b s.toNNReal)) :=
      ((hfHc (k+2) ω).sub (hfHc (k+1) ω)).comp (hpath b)
    refine (hc.intervalIntegrable u v).mono_fun
      ((hdIm k).comp (measurable_const.prodMk (hpathm b))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => ?_)
    exact norm_indicator_le_norm_self (fun p => fH (k+2) p - fH (k+1) p) (ω, b s.toNNReal)
  have hdEi (k : ℕ) (ω : Ω) (b : ContinuousPath ℂ) (u v : ℝ) :
      IntervalIntegrable (fun s : ℝ => dE k (ω, b s.toNNReal)) volume u v := by
    have hc : Continuous (fun s : ℝ =>
        M * (eR (k+2) (ω, b s.toNNReal) - eR (k+1) (ω, b s.toNNReal))) :=
      continuous_const.mul (((heRc (k+2) ω).sub (heRc (k+1) ω)).comp (hpath b))
    refine (hc.intervalIntegrable u v).mono_fun
      ((hdEm k).comp (measurable_const.prodMk (hpathm b))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => ?_)
    simp only [dE, Real.norm_eq_abs, abs_mul, abs_of_nonneg hM]
    exact mul_le_mul_of_nonneg_right (hgM _) (abs_nonneg _)
  -- the pointwise splitting before the exit time
  have hsplit (k : ℕ) (ω : Ω) (z : ℂ) (hz : ‖z‖ < ρ) :
      fH (k+2) (ω, z) - fH (k+1) (ω, z) = dI k (ω, z) + W ω * dE k (ω, z) := by
    by_cases hzI : ‖z‖ < 1/2
    · have hgz : g z = 0 := Set.indicator_of_notMem (fun h => (not_le.mpr hzI) h.1) _
      simp only [dI, dE, hgz, zero_mul, mul_zero, add_zero]
      rw [Set.indicator_of_mem (show (ω, z) ∈ Prod.snd ⁻¹' SI from hzI)]
    · have hz1 : 1/2 ≤ ‖z‖ := not_lt.mp hzI
      have hzE : z ∈ SE := ⟨hz1, hz.le⟩
      have hzpos : 0 < ‖z‖ := by linarith
      have hfac (j : ℕ) : fH (j+1) (ω, z) = W ω * (g z * eR (j+1) (ω, z)) := by
        have hsj : dyadicScale (j+1) ≤ ‖z‖ := by
          have h : dyadicScale (j+1) ≤ 1/2 := by
            simp only [dyadicScale]
            rw [pow_succ]
            have h' : (2 : ℝ)⁻¹ ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
            nlinarith
          linarith
        simp only [fH, eR, W, g, H', Set.indicator_of_mem hzE, max_eq_right hsj,
          max_eq_right hz1]
        calc dyadicScale (j+1) ^ (γ ^ 2 / 2) * Real.exp (γ * (H ω (dyadicScale (j+1)) z -
              H ω 1 0 - α * Real.log ‖z‖)) =
            dyadicScale (j+1) ^ (γ ^ 2 / 2) * (Real.exp (γ * (H ω R 0 - H ω 1 0)) *
              Real.exp (-(γ * α) * Real.log ‖z‖) *
              Real.exp (γ * (H ω (dyadicScale (j+1)) z - H ω R 0))) := by
              rw [← Real.exp_add, ← Real.exp_add]
              congr 2
              ring
          _ = _ := by ring
      have hdI0 : dI k (ω, z) = 0 :=
        Set.indicator_of_notMem (show (ω, z) ∉ Prod.snd ⁻¹' SI from hzI) _
      rw [hdI0, zero_add, show k + 2 = (k + 1) + 1 by omega, hfac (k+1), hfac k]
      simp only [dE]
      ring
  -- the exit-time increments
  let τ : ContinuousPath ℂ → ℝ≥0∞ := ContinuousPath.exitTime D
  have hτm : Measurable τ := ContinuousPath.measurable_exitTime D hDo
  let μx := planarBrownianMotion x
  have hEτ : (∫⁻ b, τ b ∂μx) ≠ ⊤ :=
    (GreenOccupation.lintegral_exitTime_planarBrownianMotion_lt_top hDo hDb x).ne
  have hfin : ∀ᵐ b ∂μx, τ b ≠ ⊤ := (ae_lt_top hτm hEτ).mono fun _ h => h.ne
  have hτ1 : (∫⁻ b, (τ b + 1) ∂μx) ≠ ⊤ := by
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    exact ENNReal.add_ne_top.mpr ⟨hEτ, ENNReal.one_ne_top⟩
  have hexit_split (k : ℕ) (ω : Ω) (b : ContinuousPath ℂ) (hb : τ b ≠ ⊤) :
      (∫ s in (0 : ℝ)..(τ b).toReal, (fH (k+2) (ω, b s.toNNReal) - fH (k+1) (ω, b s.toNNReal))) =
        (∫ s in (0 : ℝ)..(τ b).toReal, dI k (ω, b s.toNNReal)) +
          W ω * ∫ s in (0 : ℝ)..(τ b).toReal, dE k (ω, b s.toNNReal) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (hdIi k ω b _ _)
      ((hdEi k ω b _ _).const_mul _)]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(volume : Measure ℝ).ae_ne (τ b).toReal] with s hs hsI
    rw [uIoc_of_le ENNReal.toReal_nonneg] at hsI
    have hlt : s < (τ b).toReal := lt_of_le_of_ne hsI.2 hs
    have hmem : b s.toNNReal ∈ D := by
      apply ContinuousPath.mem_of_lt_exitTime D b
      have h' : ENNReal.ofReal s < ENNReal.ofReal (τ b).toReal :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hsI.1.le).mpr hlt
      rw [ENNReal.ofReal_toReal hb] at h'
      exact h'
    exact hsplit k ω _ (hDρ _ hmem)
  -- the unit-horizon bounds
  let τD : ContinuousPath ℂ → ℝ≥0 := fun b => (min 1 (τ b).toReal).toNNReal
  have hτD : Measurable τD := (measurable_const.min hτm.ennreal_toReal).real_toNNReal
  have hτD1 (b : ContinuousPath ℂ) : τD b ≤ 1 := by simp [τD]
  have hτDc (b : ContinuousPath ℂ) : ((τD b : ℝ≥0) : ℝ) = min 1 (τ b).toReal :=
    Real.coe_toNNReal _ (le_min zero_le_one ENNReal.toReal_nonneg)
  let μD : ContinuousPath ℂ → Measure ℂ := fun b =>
    Measure.map (fun t => b t)
      ((Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τD b)))
  have hμD (b : ContinuousPath ℂ) : μD b ≤ Measure.map (fun t => b t)
      (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))) :=
    Measure.map_mono Measure.restrict_le_self b.continuous.measurable
  have hμDfin (b : ContinuousPath ℂ) : IsFiniteMeasure (μD b) := by
    let : IsProbabilityMeasure (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))) :=
      ⟨by simp [Measure.map_apply continuous_real_toNNReal.measurable]⟩
    have : IsProbabilityMeasure (Measure.map (fun t => b t)
      (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) := inferInstance
    exact isFiniteMeasure_of_le _ (hμD b)
  have hintD (b : ContinuousPath ℂ) {f : ℂ → ℝ} (hf : Continuous f) : Integrable f (μD b) := by
    have : IsFiniteMeasure (μD b) := hμDfin b
    have ht : Integrable (fun s : ℝ => f (b s.toNNReal)) (volume.restrict (Icc (0 : ℝ) 1)) :=
      (hf.comp (hpath b)).integrableOn_Icc
    have hν : Integrable (fun t : ℝ≥0 => f (b t))
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))) :=
      (integrable_map_measure (hf.comp b.continuous).aestronglyMeasurable
        continuous_real_toNNReal.measurable.aemeasurable).2 ht
    exact ((integrable_map_measure hf.aestronglyMeasurable
      b.continuous.measurable.aemeasurable).2 hν).mono_measure (hμD b)
  have hIunit (k : ℕ) : ∀ y ∈ D, (∫⁻ p, ENNReal.ofReal |∫ s in (0 : ℝ)..min 1
      (ContinuousPath.exitTime D p.2).toReal, dI k (p.1, p.2 s.toNNReal)|
      ∂(P.prod (planarBrownianMotion y))) ≤ cI k := by
    intro y _
    refine le_trans (le_of_eq ?_) (hI k y μD hμD)
    apply lintegral_congr_ae
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P)
      (ν := planarBrownianMotion y)).ae hae] with p hp
    congr 2
    have hconv := intervalIntegral_path_eq_integral_occupation (fun z => dI k (p.1, z))
      ((hdIm k).comp (measurable_const.prodMk measurable_id)) p.2 (hτD1 p.2)
    rw [hτDc] at hconv
    rw [hconv]
    have hfca (j : ℕ) : (fun z => fH j (p.1, z)) = fun z => (dyadicScale j) ^ (γ ^ 2 / 2) *
        Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale j) z) := by
      funext z
      simp only [fH, hp j]
    have hind (j : ℕ) : Integrable (SI.indicator (fun z => fH j (p.1, z))) (μD p.2) :=
      (hintD p.2 (hfHc j p.1)).indicator hSI
    rw [← hfca (k+2), ← hfca (k+1), ← integral_sub (hind (k+2)) (hind (k+1))]
    congr 1
    funext z
    simp only [dI]
    by_cases hz : z ∈ SI
    · rw [Set.indicator_of_mem (show (p.1, z) ∈ Prod.snd ⁻¹' SI from hz),
        Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem (show (p.1, z) ∉ Prod.snd ⁻¹' SI from hz),
        Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, sub_zero]
  have hEunit (k : ℕ) : ∀ y ∈ D, (∫⁻ p, ENNReal.ofReal |∫ s in (0 : ℝ)..min 1
      (ContinuousPath.exitTime D p.2).toReal, dE k (p.1, p.2 s.toNNReal)|
      ∂(P.prod (planarBrownianMotion y))) ≤ cE k := by
    intro y _
    refine le_trans (le_of_eq ?_) (hE k y μD hμD)
    apply lintegral_congr_ae
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P)
      (ν := planarBrownianMotion y)).ae hHae] with p hp
    congr 2
    have hconv := intervalIntegral_path_eq_integral_occupation (fun z => dE k (p.1, z))
      ((hdEm k).comp (measurable_const.prodMk measurable_id)) p.2 (hτD1 p.2)
    rw [hτDc] at hconv
    rw [hconv]
    congr 1
    funext z
    simp only [dE, eR, hp]
  have hIexit (k : ℕ) := lintegral_ofReal_abs_exit_integral_le_of_unit hDo x (dI k) (hdIm k)
    (hdIi k) (cI k) (hIunit k) hfin
  have hEexit (k : ℕ) := lintegral_ofReal_abs_exit_integral_le_of_unit hDo x (dE k) (hdEm k)
    (hdEi k) (cE k) (hEunit k) hfin
  let ΔI : ℕ → Ω × ContinuousPath ℂ → ℝ≥0∞ := fun k p =>
    ENNReal.ofReal |∫ s in (0 : ℝ)..(τ p.2).toReal, dI k (p.1, p.2 s.toNNReal)|
  let ΔE : ℕ → Ω × ContinuousPath ℂ → ℝ≥0∞ := fun k p =>
    ENNReal.ofReal |∫ s in (0 : ℝ)..(τ p.2).toReal, dE k (p.1, p.2 s.toNNReal)|
  have hΔIm (k : ℕ) : Measurable (ΔI k) :=
    ((measurable_intervalIntegral_path (dI k) (hdIm k) (fun b => (τ b).toReal)
      hτm.ennreal_toReal (fun _ => ENNReal.toReal_nonneg)).abs).ennreal_ofReal
  have hΔEm (k : ℕ) : Measurable (ΔE k) :=
    ((measurable_intervalIntegral_path (dE k) (hdEm k) (fun b => (τ b).toReal)
      hτm.ennreal_toReal (fun _ => ENNReal.toReal_nonneg)).abs).ennreal_ofReal
  have hΔm (k : ℕ) : Measurable (fun p => ΔI k p + ΔE k p) := (hΔIm k).add (hΔEm k)
  have hsumΔ : (∫⁻ p, ∑' k, (ΔI k p + ΔE k p) ∂(P.prod μx)) ≠ ⊤ := by
    rw [lintegral_tsum (fun k => (hΔm k).aemeasurable)]
    have hle (k : ℕ) : (∫⁻ p, (ΔI k p + ΔE k p) ∂(P.prod μx)) ≤
        (cI k + cE k) * ∫⁻ b, (τ b + 1) ∂μx := by
      rw [lintegral_add_left (hΔIm k), add_mul]
      exact add_le_add (hIexit k) (hEexit k)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_add]
    exact ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨hcI, hcE⟩) hτ1
  have hΔsm : Measurable (fun p => ∑' k, (ΔI k p + ΔE k p)) := Measurable.tsum hΔm
  have hquench : ∀ᵐ ω ∂P, (∫⁻ b, ∑' k, (ΔI k (ω, b) + ΔE k (ω, b)) ∂μx) ≠ ⊤ := by
    have h := lintegral_prod _ hΔsm.aemeasurable (μ := P) (ν := μx)
    rw [h] at hsumΔ
    exact (ae_lt_top hΔsm.lintegral_prod_right' hsumΔ).mono fun _ h => h.ne
  have happ : ∀ᵐ ω ∂P, ∀ k : ℕ, lqgClockApprox γ (H' ω) (dyadicScale k) =
      lqgClockApprox γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) (dyadicScale k) := by
    filter_upwards [hae] with ω hω k
    funext b t
    simp only [lqgClockApprox, hω k]
  have hclock' : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ (H' ω) x (F ω) := by
    filter_upwards [hclock, happ] with ω h hω
    intro T η hη
    simpa only [hω] using h T η hη
  filter_upwards [hquench, hclock', hF, hae] with ω hq hcl hFω hω
  have happrox (j : ℕ) (b : ContinuousPath ℂ) :
      lqgClockApprox γ (H' ω) (dyadicScale j) b (τ b).toNNReal =
        ∫ s in (0 : ℝ)..(τ b).toReal, fH j (ω, b s.toNNReal) := by
    simp only [lqgClockApprox, ENNReal.coe_toNNReal_eq_toReal, fH]
  let m : ℝ≥0∞ := ENNReal.ofReal (max 1 (W ω))
  have hm1 : (1 : ℝ≥0∞) ≤ m := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hmW : ENNReal.ofReal (W ω) ≤ m := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hpt : ∀ᵐ b ∂μx, (∑' k, ENNReal.ofReal
      |lqgClockApprox γ (H' ω) (dyadicScale (k+2)) b (ContinuousPath.exitTime D b).toNNReal -
        lqgClockApprox γ (H' ω) (dyadicScale (k+1)) b (ContinuousPath.exitTime D b).toNNReal|) ≤
      m * ∑' k, (ΔI k (ω, b) + ΔE k (ω, b)) := by
    filter_upwards [hfin] with b hb
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro k
    have hdiff : lqgClockApprox γ (H' ω) (dyadicScale (k+2)) b (τ b).toNNReal -
        lqgClockApprox γ (H' ω) (dyadicScale (k+1)) b (τ b).toNNReal =
        ∫ s in (0 : ℝ)..(τ b).toReal,
          (fH (k+2) (ω, b s.toNNReal) - fH (k+1) (ω, b s.toNNReal)) := by
      have h2 : IntervalIntegrable (fun s : ℝ => fH (k+2) (ω, b s.toNNReal)) volume 0
          (τ b).toReal := ((hfHc (k+2) ω).comp (hpath b)).intervalIntegrable _ _
      have h1 : IntervalIntegrable (fun s : ℝ => fH (k+1) (ω, b s.toNNReal)) volume 0
          (τ b).toReal := ((hfHc (k+1) ω).comp (hpath b)).intervalIntegrable _ _
      rw [happrox, happrox, ← intervalIntegral.integral_sub h2 h1]
    change ENNReal.ofReal |lqgClockApprox γ (H' ω) (dyadicScale (k+2)) b (τ b).toNNReal -
        lqgClockApprox γ (H' ω) (dyadicScale (k+1)) b (τ b).toNNReal| ≤ _
    rw [hdiff, hexit_split k ω b hb]
    have hW0 : 0 ≤ W ω := (Real.exp_pos _).le
    calc ENNReal.ofReal |(∫ s in (0 : ℝ)..(τ b).toReal, dI k (ω, b s.toNNReal)) +
          W ω * ∫ s in (0 : ℝ)..(τ b).toReal, dE k (ω, b s.toNNReal)|
        ≤ ENNReal.ofReal (|∫ s in (0 : ℝ)..(τ b).toReal, dI k (ω, b s.toNNReal)| +
          W ω * |∫ s in (0 : ℝ)..(τ b).toReal, dE k (ω, b s.toNNReal)|) := by
          apply ENNReal.ofReal_le_ofReal
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_of_nonneg hW0]
      _ = ΔI k (ω, b) + ENNReal.ofReal (W ω) * ΔE k (ω, b) := by
          rw [ENNReal.ofReal_add (abs_nonneg _) (mul_nonneg hW0 (abs_nonneg _)),
            ENNReal.ofReal_mul hW0]
      _ ≤ m * ΔI k (ω, b) + m * ΔE k (ω, b) := by
          gcongr
          calc ΔI k (ω, b) = 1 * ΔI k (ω, b) := (one_mul _).symm
            _ ≤ m * ΔI k (ω, b) := by gcongr
      _ = m * (ΔI k (ω, b) + ΔE k (ω, b)) := (mul_add _ _ _).symm
  have hsumω : (∫⁻ b, ∑' k, ENNReal.ofReal
      |lqgClockApprox γ (H' ω) (dyadicScale (k+2)) b (ContinuousPath.exitTime D b).toNNReal -
        lqgClockApprox γ (H' ω) (dyadicScale (k+1)) b (ContinuousPath.exitTime D b).toNNReal|
      ∂(planarBrownianMotion x)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hpt)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq
  have hui := uniformIntegrable_exit_clockApprox_of_lintegral_tsum_ne_top (γ := γ)
    (fun k => hH'c k ω) hDo hDb x hsumω
  obtain ⟨-, -, hne, -, htend⟩ :=
    tendsto_clockApprox_green_expectedLBMExitTime_of_uniformIntegrable hD hx
      (fun k => hH'c k ω) hcl hFω hui
  simpa only [hω] using (⟨hne, htend⟩ : expectedLBMExitTime (F ω) D x ≠ ⊤ ∧ _)

/-- The expected exit time of the inserted clock for a nonpositive insertion: for `α ≤ 0` and
`0 < γ < 2`, every LQG clock from a fixed start in a smooth bounded domain that is almost surely
a time-change clock has, for almost every field, finite expected LBM exit time equal to the
limit of the expected Green integrals of the approximating measures. -/
theorem ae_tendsto_clockApprox_green_expectedLBMExitTime_of_nonpos
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hα : α ≤ 0) (hγ : 0 < γ)
    (hγ2 : γ < 2) {D : Set ℂ} (hD : IsSmoothBoundedOpen D) {x : ℂ} (hx : x ∈ D)
    (F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hclock : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) x (F ω))
    (hF : ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F ω b)) :
    ∀ᵐ ω ∂P, expectedLBMExitTime (F ω) D x ≠ ⊤ ∧
      Tendsto (fun k : ℕ => ∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) *
        ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) y)))
        atTop (𝓝 (expectedLBMExitTime (F ω) D x)) := by
  obtain ⟨cI, hcI, hI⟩ := exists_summable_uniform_inner_suboccupation_increment_bound_of_nonpos
    hh hα hγ hγ2 (δ := 1/2) (by norm_num) le_rfl
  exact ae_tendsto_clockApprox_green_expectedLBMExitTime_of_halfDisc_increments hh hγ hγ2 hD hx
    cI hcI hI F hclock hF

/-- The expected exit time of the inserted clock for a positive insertion in the range
`γ ^ 2 / 2 < 2 - γ * α`: every LQG clock from a fixed start in a smooth bounded domain that is
almost surely a time-change clock has, for almost every field, finite expected LBM exit time
equal to the limit of the expected Green integrals of the approximating measures. -/
theorem ae_tendsto_clockApprox_green_expectedLBMExitTime_of_lt_two_sub
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hq0 : 0 < γ * α)
    (hγ : 0 < γ) (hsub : γ ^ 2 / 2 < 2 - γ * α) {D : Set ℂ} (hD : IsSmoothBoundedOpen D)
    {x : ℂ} (hx : x ∈ D) (F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hclock : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) x (F ω))
    (hF : ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F ω b)) :
    ∀ᵐ ω ∂P, expectedLBMExitTime (F ω) D x ≠ ⊤ ∧
      Tendsto (fun k : ℕ => ∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) *
        ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) y)))
        atTop (𝓝 (expectedLBMExitTime (F ω) D x)) := by
  have hγ2 : γ < 2 := by nlinarith
  obtain ⟨cI, hcI, hI⟩ := exists_summable_uniform_inner_suboccupation_increment_bound hh hq0 hγ
    hsub (δ := 1/2) (by norm_num) le_rfl
  exact ae_tendsto_clockApprox_green_expectedLBMExitTime_of_halfDisc_increments hh hγ hγ2 hD hx
    cI hcI hI F hclock hF

end HarmonicBalls
