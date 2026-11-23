import HarmonicBalls.Proofs.Potential.LQGClockExitAlmostEveryStartSummability

/-!
# Summable exit-time increments of weighted clock approximations, for every insertion

Let `D` be a bounded open set, `m ∈ ℕ`, and `φ` a continuous weight with values in `[0, 1]`
vanishing on the disc `‖z‖ < 2^{-m}` around the insertion point. At the dyadic scales
`ε ≤ 2^{-m}` and at points `‖z‖ ≥ 2^{-m}` the inserted clock density is the density of the field
normalized at radius `R`, times the random constant `exp (γ (h_R(0) - h_1(0)))` and the bounded
weight `|z|^{-γ α}`. The weighted increments `φ (f_{k+m+2} - f_{k+m+1})` therefore have the
summable unit-horizon bounds of the bounded-weight estimate, uniform over the start, for every
insertion `α` and every `0 < γ < 2`. As for the unweighted approximations, for almost every field
the quenched expected sum of the exit-time increments of the weighted approximations is finite
for Lebesgue almost every start in `D`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

set_option maxHeartbeats 400000 in
/-- Summable exit-time increments of weighted clock approximations from almost every start: for
a continuous weight `φ` with values in `[0, 1]` vanishing on `‖z‖ < 2^{-m}`, for every insertion
`α` and `0 < γ < 2`, for almost every field and Lebesgue almost every start `y` in a bounded
open set `D`, the expected sum over `k` of the absolute increments of
`∫_0^{τ_D} φ(b_s) f_{k+m}(b_s) ds` is finite under Brownian motion from `y`, where
`f_j = ε_j^{γ²/2} e^{γ h_{ε_j}}` at `ε_j = 2^{-j}`. -/
theorem ae_ae_lintegral_tsum_exit_weighted_increment_ne_top
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ} (α : ℝ) (hγ : 0 < γ)
    (hγ2 : γ < 2) {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D) (m : ℕ)
    {φ : ℂ → ℝ} (hφc : Continuous φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1)
    (hφδ : ∀ z, ‖z‖ < dyadicScale m → φ z = 0) :
    ∀ᵐ ω ∂P, ∀ᵐ y ∂(volume.restrict D), (∫⁻ b, ∑' k, ENNReal.ofReal
      |(∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, φ (b s.toNNReal) *
          (dyadicScale (k + 2 + m) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (k + 2 + m))
              (b s.toNNReal)))) -
        ∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, φ (b s.toNNReal) *
          (dyadicScale (k + 1 + m) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (k + 1 + m))
              (b s.toNNReal)))| ∂(planarBrownianMotion y)) ≠ ⊤ := by
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
  let δ : ℝ := dyadicScale m
  have hδ : 0 < δ := dyadicScale_pos m
  let SE : Set ℂ := {z : ℂ | ‖z‖ ≤ ρ}
  have hSE : MeasurableSet SE := measurableSet_le measurable_norm measurable_const
  let e : ℂ → ℝ := fun z => Real.exp (-(γ * α) * Real.log (max δ ‖z‖))
  have hec : Continuous e := Real.continuous_exp.comp (continuous_const.mul
    ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hδ).ne')))
  let g : ℂ → ℝ := SE.indicator (fun z => φ z * e z)
  have hgm : Measurable g := (hφc.mul hec).measurable.indicator hSE
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn hec.continuousOn
  let M : ℝ := max K 0
  have hM : 0 ≤ M := le_max_right _ _
  have hgM : ∀ z, |g z| ≤ M := by
    intro z
    by_cases hz : z ∈ SE
    · have hzb : z ∈ Metric.closedBall (0 : ℂ) ρ := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hz
      have hk := hK z hzb
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hk
      simp only [g, Set.indicator_of_mem hz]
      rw [abs_of_nonneg (mul_nonneg (hφ0 z) (Real.exp_pos _).le)]
      calc φ z * e z ≤ 1 * e z := mul_le_mul_of_nonneg_right (hφ1 z) (Real.exp_pos _).le
        _ = e z := one_mul _
        _ ≤ M := hk.trans (le_max_left _ _)
    · simp only [g, Set.indicator_of_notMem hz, abs_zero]
      exact hM
  have hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ R - 1/2 := by
    intro z hz
    have hzE : z ∈ SE := by
      by_contra h
      exact hz (Set.indicator_of_notMem h _)
    simp only [R]
    linarith [show ‖z‖ ≤ ρ from hzE]
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
  let dE : ℕ → Ω × ℂ → ℝ := fun k p => g p.2 * (eR (k+m+2) p - eR (k+m+1) p)
  have hdEm (k : ℕ) : Measurable (dE k) :=
    (hgm.comp measurable_snd).mul ((heRm (k+m+2)).sub (heRm (k+m+1)))
  let W : Ω → ℝ := fun ω => Real.exp (γ * (H ω R 0 - H ω 1 0))
  have hpath (b : ContinuousPath ℂ) : Continuous (fun s : ℝ => b s.toNNReal) :=
    b.continuous.comp continuous_real_toNNReal
  have hpathm (b : ContinuousPath ℂ) : Measurable (fun s : ℝ => b s.toNNReal) :=
    (hpath b).measurable
  have hdEi (k : ℕ) (ω : Ω) (b : ContinuousPath ℂ) (u v : ℝ) :
      IntervalIntegrable (fun s : ℝ => dE k (ω, b s.toNNReal)) volume u v := by
    have hc : Continuous (fun s : ℝ =>
        M * (eR (k+m+2) (ω, b s.toNNReal) - eR (k+m+1) (ω, b s.toNNReal))) :=
      continuous_const.mul (((heRc (k+m+2) ω).sub (heRc (k+m+1) ω)).comp (hpath b))
    refine (hc.intervalIntegrable u v).mono_fun
      ((hdEm k).comp (measurable_const.prodMk (hpathm b))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => ?_)
    simp only [dE, Real.norm_eq_abs, abs_mul, abs_of_nonneg hM]
    exact mul_le_mul_of_nonneg_right (hgM _) (abs_nonneg _)
  -- the weighted densities
  let fφ : ℕ → Ω × ℂ → ℝ := fun j p => φ p.2 * fH (j + m) p
  have hfφc (j : ℕ) (ω : Ω) : Continuous (fun z => fφ j (ω, z)) :=
    hφc.mul (hfHc (j + m) ω)
  -- the pointwise splitting before the exit time
  have hsplit (k : ℕ) (ω : Ω) (z : ℂ) (hz : ‖z‖ < ρ) :
      fφ (k+2) (ω, z) - fφ (k+1) (ω, z) = W ω * dE k (ω, z) := by
    have hzE : z ∈ SE := hz.le
    by_cases hzδ : ‖z‖ < δ
    · simp only [fφ, dE, g, Set.indicator_of_mem hzE, hφδ z hzδ, zero_mul, sub_zero, mul_zero]
    · have hz1 : δ ≤ ‖z‖ := not_lt.mp hzδ
      have hfac (j : ℕ) (hj : m ≤ j) : fH j (ω, z) = W ω * (e z * eR j (ω, z)) := by
        have hsj : dyadicScale j ≤ ‖z‖ := by
          refine le_trans ?_ hz1
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
        simp only [fH, eR, W, e, H', max_eq_right hsj, max_eq_right hz1]
        calc dyadicScale j ^ (γ ^ 2 / 2) * Real.exp (γ * (H ω (dyadicScale j) z -
              H ω 1 0 - α * Real.log ‖z‖)) =
            dyadicScale j ^ (γ ^ 2 / 2) * (Real.exp (γ * (H ω R 0 - H ω 1 0)) *
              Real.exp (-(γ * α) * Real.log ‖z‖) *
              Real.exp (γ * (H ω (dyadicScale j) z - H ω R 0))) := by
              rw [← Real.exp_add, ← Real.exp_add]
              congr 2
              ring
          _ = _ := by ring
      simp only [fφ, dE, g, Set.indicator_of_mem hzE]
      rw [show k + 2 + m = k + m + 2 by omega, show k + 1 + m = k + m + 1 by omega,
        hfac (k+m+2) (by omega), hfac (k+m+1) (by omega)]
      ring
  -- the exit-time increments
  let τ : ContinuousPath ℂ → ℝ≥0∞ := ContinuousPath.exitTime D
  have hτm : Measurable τ := ContinuousPath.measurable_exitTime D hDo
  have hexit_split (k : ℕ) (ω : Ω) (b : ContinuousPath ℂ) (hb : τ b ≠ ⊤) :
      (∫ s in (0 : ℝ)..(τ b).toReal, (fφ (k+2) (ω, b s.toNNReal) - fφ (k+1) (ω, b s.toNNReal))) =
        W ω * ∫ s in (0 : ℝ)..(τ b).toReal, dE k (ω, b s.toNNReal) := by
    rw [← intervalIntegral.integral_const_mul]
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
  have hEunit (k : ℕ) : ∀ y ∈ D, (∫⁻ p, ENNReal.ofReal |∫ s in (0 : ℝ)..min 1
      (ContinuousPath.exitTime D p.2).toReal, dE k (p.1, p.2 s.toNNReal)|
      ∂(P.prod (planarBrownianMotion y))) ≤ cE (k + m) := by
    intro y _
    refine le_trans (le_of_eq ?_) (hE (k + m) y μD hμD)
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
  let ΔE : ℕ → Ω × ContinuousPath ℂ → ℝ≥0∞ := fun k p =>
    ENNReal.ofReal |∫ s in (0 : ℝ)..(τ p.2).toReal, dE k (p.1, p.2 s.toNNReal)|
  have hΔEm (k : ℕ) : Measurable (ΔE k) :=
    ((measurable_intervalIntegral_path (dE k) (hdEm k) (fun b => (τ b).toReal)
      hτm.ennreal_toReal (fun _ => ENNReal.toReal_nonneg)).abs).ennreal_ofReal
  have hΔsm : Measurable (fun p => ∑' k, ΔE k p) := Measurable.tsum hΔEm
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
  have hsumΔ (y : ℂ) : (∫⁻ p, ∑' k, ΔE k p ∂(P.prod (planarBrownianMotion y))) ≤
      (∑' k, cE (k + m)) * (Cτ + 1) := by
    rw [lintegral_tsum (fun k => (hΔEm k).aemeasurable), ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun k => ?_
    exact (lintegral_ofReal_abs_exit_integral_le_of_unit hDo y (dE k) (hdEm k) (hdEi k)
      (cE (k + m)) (hEunit k) (hfin y)).trans (by gcongr; exact hτ1 y)
  have hKfin : (∑' k, cE (k + m)) * (Cτ + 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (ne_top_of_le_ne_top hcE
      (ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective m) cE))
      (ENNReal.add_ne_top.mpr ⟨hCτ.ne, ENNReal.one_ne_top⟩)
  -- the quenched sums over the starts in the domain
  let G : Ω × ℂ → ℝ≥0∞ := fun q =>
    ∫⁻ b, ∑' k, ΔE k (q.1, b) ∂(planarBrownianMotion q.2)
  have hGm : Measurable G := by
    have h := Measurable.lintegral_kernel_prod_right'
      (κ := planarBrownianMotion.comap Prod.snd measurable_snd)
      (f := fun r : (Ω × ℂ) × ContinuousPath ℂ => ∑' k, ΔE k (r.1.1, r.2))
      (hΔsm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    simpa only [Kernel.comap_apply] using h
  have hDvol : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hint : (∫⁻ ω, (∫⁻ y in D, G (ω, y)) ∂P) ≠ ⊤ := by
    have hswap := lintegral_lintegral_swap (μ := P) (ν := volume.restrict D)
      (f := fun ω y => G (ω, y)) hGm.aemeasurable
    rw [hswap]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hKfin hDvol) ?_
    rw [← setLIntegral_const]
    refine lintegral_mono fun y => ?_
    have hprod := lintegral_prod (μ := P) (ν := planarBrownianMotion y) _ hΔsm.aemeasurable
    rw [← hprod]
    exact hsumΔ y
  have hq : ∀ᵐ ω ∂P, (∫⁻ y in D, G (ω, y)) ≠ ⊤ :=
    (ae_lt_top hGm.lintegral_prod_right' hint).mono fun _ h => h.ne
  filter_upwards [hq, hae] with ω hqω hω
  filter_upwards [(ae_lt_top (hGm.comp measurable_prodMk_left) hqω)] with y hy
  have happrox (j : ℕ) (b : ContinuousPath ℂ) :
      (∫ s in (0 : ℝ)..(τ b).toReal, φ (b s.toNNReal) * (dyadicScale (j + m) ^ (γ ^ 2 / 2) *
        Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (j + m))
          (b s.toNNReal)))) = ∫ s in (0 : ℝ)..(τ b).toReal, fφ j (ω, b s.toNNReal) := by
    simp only [fφ, fH, hω (j + m)]
  let mW : ℝ≥0∞ := ENNReal.ofReal (W ω)
  have hpt : ∀ᵐ b ∂(planarBrownianMotion y), (∑' k, ENNReal.ofReal
      |(∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, φ (b s.toNNReal) *
          (dyadicScale (k + 2 + m) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (k + 2 + m))
              (b s.toNNReal)))) -
        ∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, φ (b s.toNNReal) *
          (dyadicScale (k + 1 + m) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (k + 1 + m))
              (b s.toNNReal)))|) ≤ mW * ∑' k, ΔE k (ω, b) := by
    filter_upwards [hfin y] with b hb
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun k => ?_
    have h2 : IntervalIntegrable (fun s : ℝ => fφ (k+2) (ω, b s.toNNReal)) volume 0
        (τ b).toReal := ((hfφc (k+2) ω).comp (hpath b)).intervalIntegrable _ _
    have h1 : IntervalIntegrable (fun s : ℝ => fφ (k+1) (ω, b s.toNNReal)) volume 0
        (τ b).toReal := ((hfφc (k+1) ω).comp (hpath b)).intervalIntegrable _ _
    have hW0 : 0 ≤ W ω := (Real.exp_pos _).le
    change ENNReal.ofReal
        |(∫ s in (0 : ℝ)..(τ b).toReal, φ (b s.toNNReal) *
          (dyadicScale (k + 2 + m) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (k + 2 + m))
              (b s.toNNReal)))) -
        ∫ s in (0 : ℝ)..(τ b).toReal, φ (b s.toNNReal) *
          (dyadicScale (k + 1 + m) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (k + 1 + m))
              (b s.toNNReal)))| ≤ _
    rw [happrox (k+2), happrox (k+1), ← intervalIntegral.integral_sub h2 h1,
      hexit_split k ω b hb, abs_mul, abs_of_nonneg hW0, ENNReal.ofReal_mul hW0]
  refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hpt)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hy.ne

end HarmonicBalls
