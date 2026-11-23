import HarmonicBalls.Proofs.Potential.LQGClockExitExpectationIdentity
import HarmonicBalls.Proofs.Potential.LQGClockAnnularScaleRecursion

/-!
# Summable exit-time increments of the inserted clock from almost every start

Let `D` be a bounded open set. The proof of
`ae_tendsto_clockApprox_green_expectedLBMExitTime_of_halfDisc_increments` bounds, for every start
`y`, the expected sum over the dyadic scales of the exit-time increments of the clock
approximations under the joint law of the field and the Brownian path from `y` by a constant
times `E_y[τ_D] + 1`, where the constant does not depend on `y` (summable half-disc and
bounded-weight increment bounds, uniform over the start), up to the random constant
`exp (γ (h_R(0) - h_1(0)))`. The expected exit times are bounded uniformly in the start.
Integrating over the starts in `D` and exchanging the integrals, for almost every field the
quenched expected sum of the exit-time increments is finite for Lebesgue almost every start
in `D`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

private theorem exists_exterior_weight_bound' (γ α ρ : ℝ) :
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
/-- Summable exit-time increments from almost every start: under summable half-disc increment
bounds uniform over the start, for almost every field and Lebesgue almost every start `y` in a
bounded open set `D`, the expected sum over the dyadic scales of the absolute increments of the
clock approximations read at the exit time from `D` is finite under Brownian motion from `y`. -/
theorem ae_ae_lintegral_tsum_exit_clockApprox_increment_ne_top_of_halfDisc_increments
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D)
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
            ∂(μ p.2)| ∂(P.prod (planarBrownianMotion y))) ≤ cI k) :
    ∀ᵐ ω ∂P, ∀ᵐ y ∂(volume.restrict D), (∫⁻ b, ∑' k, ENNReal.ofReal
      |lqgClockApprox γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) (dyadicScale (k+2)) b
          (ContinuousPath.exitTime D b).toNNReal -
        lqgClockApprox γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) (dyadicScale (k+1)) b
          (ContinuousPath.exitTime D b).toNNReal| ∂(planarBrownianMotion y)) ≠ ⊤ := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
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
  obtain ⟨M, hM, hgM⟩ := exists_exterior_weight_bound' γ α ρ
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
  have hΔm (k : ℕ) : Measurable (fun p => ΔI k p + ΔE k p) := (hΔIm k).add (hΔEm k)
  have hΔsm : Measurable (fun p => ∑' k, (ΔI k p + ΔE k p)) := Measurable.tsum hΔm
  obtain ⟨Cτ, hCτ, hCτb⟩ := exists_uniform_lintegral_exitTime_rpow_le hDo hDb zero_le_one
    one_le_two
  have hfin (y : ℂ) : ∀ᵐ b ∂(planarBrownianMotion y), τ b ≠ ⊤ :=
    (ae_lt_top hτm (GreenOccupation.lintegral_exitTime_planarBrownianMotion_lt_top hDo hDb
      y).ne).mono fun _ h => h.ne
  have hτ1 (y : ℂ) : (∫⁻ b, (τ b + 1) ∂(planarBrownianMotion y)) ≤ Cτ + 1 := by
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    gcongr
    calc (∫⁻ b, τ b ∂(planarBrownianMotion y)) =
        ∫⁻ b, (ENNReal.ofReal (τ b).toReal) ^ (1 : ℝ) ∂(planarBrownianMotion y) := by
          apply lintegral_congr_ae
          filter_upwards [hfin y] with b hb
          rw [ENNReal.rpow_one, ENNReal.ofReal_toReal hb]
      _ ≤ Cτ := hCτb y
  have hsumΔ (y : ℂ) : (∫⁻ p, ∑' k, (ΔI k p + ΔE k p) ∂(P.prod (planarBrownianMotion y))) ≤
      (∑' k, (cI k + cE k)) * (Cτ + 1) := by
    rw [lintegral_tsum (fun k => (hΔm k).aemeasurable), ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun k => ?_
    rw [lintegral_add_left (hΔIm k), add_mul]
    exact add_le_add
      ((lintegral_ofReal_abs_exit_integral_le_of_unit hDo y (dI k) (hdIm k) (hdIi k) (cI k)
        (hIunit k) (hfin y)).trans (by gcongr; exact hτ1 y))
      ((lintegral_ofReal_abs_exit_integral_le_of_unit hDo y (dE k) (hdEm k) (hdEi k) (cE k)
        (hEunit k) (hfin y)).trans (by gcongr; exact hτ1 y))
  have hKfin : (∑' k, (cI k + cE k)) * (Cτ + 1) ≠ ⊤ := by
    rw [ENNReal.tsum_add]
    exact ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨hcI, hcE⟩)
      (ENNReal.add_ne_top.mpr ⟨hCτ.ne, ENNReal.one_ne_top⟩)
  -- the quenched sums over the starts in the domain
  let g : Ω × ℂ → ℝ≥0∞ := fun q =>
    ∫⁻ b, ∑' k, (ΔI k (q.1, b) + ΔE k (q.1, b)) ∂(planarBrownianMotion q.2)
  have hgm : Measurable g := by
    have h := Measurable.lintegral_kernel_prod_right'
      (κ := planarBrownianMotion.comap Prod.snd measurable_snd)
      (f := fun r : (Ω × ℂ) × ContinuousPath ℂ => ∑' k, (ΔI k (r.1.1, r.2) + ΔE k (r.1.1, r.2)))
      (hΔsm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    simpa only [Kernel.comap_apply] using h
  have hDvol : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hint : (∫⁻ ω, (∫⁻ y in D, g (ω, y)) ∂P) ≠ ⊤ := by
    have hswap := lintegral_lintegral_swap (μ := P) (ν := volume.restrict D)
      (f := fun ω y => g (ω, y)) hgm.aemeasurable
    rw [hswap]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hKfin hDvol) ?_
    rw [← setLIntegral_const]
    refine lintegral_mono fun y => ?_
    have hprod := lintegral_prod (μ := P) (ν := planarBrownianMotion y) _ hΔsm.aemeasurable
    rw [← hprod]
    exact hsumΔ y
  have hq : ∀ᵐ ω ∂P, (∫⁻ y in D, g (ω, y)) ≠ ⊤ :=
    (ae_lt_top hgm.lintegral_prod_right' hint).mono fun _ h => h.ne
  filter_upwards [hq, hae] with ω hqω hω
  filter_upwards [(ae_lt_top (hgm.comp measurable_prodMk_left) hqω)] with y hy
  have happrox (j : ℕ) (b : ContinuousPath ℂ) :
      lqgClockApprox γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) (dyadicScale j) b
        (τ b).toNNReal = ∫ s in (0 : ℝ)..(τ b).toReal, fH j (ω, b s.toNNReal) := by
    simp only [lqgClockApprox, ENNReal.coe_toNNReal_eq_toReal, fH, hω j]
  let m : ℝ≥0∞ := ENNReal.ofReal (max 1 (W ω))
  have hm1 : (1 : ℝ≥0∞) ≤ m := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hmW : ENNReal.ofReal (W ω) ≤ m := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hpt : ∀ᵐ b ∂(planarBrownianMotion y), (∑' k, ENNReal.ofReal
      |lqgClockApprox γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) (dyadicScale (k+2)) b
          (ContinuousPath.exitTime D b).toNNReal -
        lqgClockApprox γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) (dyadicScale (k+1)) b
          (ContinuousPath.exitTime D b).toNNReal|) ≤
      m * ∑' k, (ΔI k (ω, b) + ΔE k (ω, b)) := by
    filter_upwards [hfin y] with b hb
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro k
    have hdiff :
        lqgClockApprox γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) (dyadicScale (k+2)) b
          (τ b).toNNReal -
        lqgClockApprox γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) (dyadicScale (k+1)) b
          (τ b).toNNReal =
        ∫ s in (0 : ℝ)..(τ b).toReal,
          (fH (k+2) (ω, b s.toNNReal) - fH (k+1) (ω, b s.toNNReal)) := by
      have h2 : IntervalIntegrable (fun s : ℝ => fH (k+2) (ω, b s.toNNReal)) volume 0
          (τ b).toReal := ((hfHc (k+2) ω).comp (hpath b)).intervalIntegrable _ _
      have h1 : IntervalIntegrable (fun s : ℝ => fH (k+1) (ω, b s.toNNReal)) volume 0
          (τ b).toReal := ((hfHc (k+1) ω).comp (hpath b)).intervalIntegrable _ _
      rw [happrox, happrox, ← intervalIntegral.integral_sub h2 h1]
    change ENNReal.ofReal
        |lqgClockApprox γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) (dyadicScale (k+2)) b
          (τ b).toNNReal -
        lqgClockApprox γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) (dyadicScale (k+1)) b
          (τ b).toNNReal| ≤ _
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
  refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hpt)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hy.ne

end HarmonicBalls
