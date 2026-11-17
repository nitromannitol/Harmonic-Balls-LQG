import HarmonicBalls.Proofs.Potential.BrownianStoppedOccupationNoAtoms
import HarmonicBalls.Proofs.Potential.LogPotentialExceptionalSet

/-! # Logarithmic potentials of stopped Brownian occupation

Uniform occupation bounds control singular potentials of the stopped measure.
-/

open MeasureTheory MarkovProcess Set Metric Filter
open scoped ENNReal NNReal Topology

namespace HarmonicBalls

/-- A stopped occupation measure has mass equal to the finite extended exit time. -/
theorem stoppedBrownianOccupation_univ (D : Set ℂ) (b : ContinuousPath ℂ)
    (hfin : ContinuousPath.exitTime D b ≠ ∞) :
    stoppedBrownianOccupation D b univ = ContinuousPath.exitTime D b := by
  have hm : Measurable (fun t : ℝ => b t.toNNReal) :=
    b.continuous.measurable.comp continuous_real_toNNReal.measurable
  rw [stoppedBrownianOccupation, Measure.map_apply hm MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]
  have hs := ContinuousPath.survivalSet_ne_top (ContinuousPath.exitTime D b) hfin
  have heq : {t : ℝ | 0 < t ∧ ((t.toNNReal : ℝ≥0) : ℝ≥0∞) <
      ContinuousPath.exitTime D b} = Ioo 0 (ContinuousPath.exitTime D b).toReal := by
    simpa [Set.inter_def, and_comm] using hs
  rw [heq, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal hfin]

/-- A finite measure with a uniform linear ball bound has uniformly bounded Riesz potentials. -/
theorem lintegral_riesz_le_of_uniform_ball {μ : Measure ℂ} {m C : ℝ}
    (hm : 0 ≤ m) (hC : 0 ≤ C) (hμ : μ univ ≤ ENNReal.ofReal m)
    (hball : ∀ z : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 →
      μ (ball z r) ≤ ENNReal.ofReal (C * r)) (z : ℂ) :
    ∫⁻ w, ENNReal.ofReal (‖z - w‖ ^ (-(1 / 2 : ℝ))) ∂μ ≤
      ENNReal.ofReal (m + 2 * (C + m)) := by
  have hA : 0 ≤ 2 * (C + m) := by positivity
  have hclosed : ∀ r : ℝ, 0 < r → μ (closedBall z r) ≤
      ENNReal.ofReal (2 * (C + m) * r ^ (1 : ℝ)) := by
    intro r hr
    rw [Real.rpow_one]
    by_cases hrhalf : 2 * r ≤ 1
    · calc μ (closedBall z r) ≤ μ (ball z (2 * r)) :=
            measure_mono (closedBall_subset_ball (by linarith))
        _ ≤ ENNReal.ofReal (C * (2 * r)) := hball z _ (by linarith) hrhalf
        _ ≤ ENNReal.ofReal (2 * (C + m) * r) := ENNReal.ofReal_le_ofReal (by nlinarith)
    · calc μ (closedBall z r) ≤ μ univ := measure_mono (subset_univ _)
        _ ≤ ENNReal.ofReal m := hμ
        _ ≤ ENNReal.ofReal (2 * (C + m) * r) := ENNReal.ofReal_le_ofReal (by nlinarith)
  have h := lintegral_norm_sub_rpow_neg_le (ν := μ) (x := z) (m := m)
    (A := 2 * (C + m)) (α := (1 / 2 : ℝ)) (β := 1)
    (by norm_num) (by norm_num) hm hA hμ hclosed
  convert h using 1; norm_num

/-- A single full-mass event bounds all half-order Riesz potentials for all bounded domains. -/
theorem planarBrownianMotion_stopped_uniform_riesz_potential (x : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ D : Set ℂ, Bornology.IsBounded D →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ,
        ∫⁻ w, ENNReal.ofReal (‖z - w‖ ^ (-(1 / 2 : ℝ)))
          ∂(stoppedBrownianOccupation D b) ≤ ENNReal.ofReal K := by
  have hballs : ∀ᵐ b ∂(planarBrownianMotion x), ∀ n : ℕ,
      ContinuousPath.exitTime (ball x (n : ℝ)) b < ∞ := by
    simp only [ae_all_iff]
    exact fun n => Section6.ae_planarBrownianMotion_exitTime_ball_lt_top x n
  filter_upwards [planarBrownianMotion_uniform_ball_occupation_all_horizons x,
    hballs] with b hb hball D hD
  obtain ⟨R, hR⟩ := hD.subset_ball x
  obtain ⟨n, hn⟩ := exists_nat_ge R
  have hsub : D ⊆ ball x (n : ℝ) := hR.trans (ball_subset_ball hn)
  have hfin : ContinuousPath.exitTime D b < ∞ :=
    lt_of_le_of_lt (ContinuousPath.exitTime_mono hsub b) (hball n)
  obtain ⟨C, hC, hbound⟩ := hb (ContinuousPath.exitTime D b).toReal 1 (by norm_num) (by norm_num)
  let m := (ContinuousPath.exitTime D b).toReal
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  have hμ : stoppedBrownianOccupation D b univ ≤ ENNReal.ofReal m := by
    rw [stoppedBrownianOccupation_univ D b hfin.ne, ENNReal.ofReal_toReal hfin.ne]
  refine ⟨m + 2 * (C + m), by positivity, fun z =>
    lintegral_riesz_le_of_uniform_ball hm hC.le hμ ?_ z⟩
  intro y r hr hr1
  calc stoppedBrownianOccupation D b (ball y r) ≤
      volume {t : ℝ | t ∈ Icc (0 : ℝ) m ∧ ‖b t.toNNReal - y‖ < r} :=
        stoppedBrownianOccupation_ball_le D b hfin.ne y r
    _ ≤ ENNReal.ofReal (C * r) := by simpa using hbound y r hr hr1

/-- A compactly supported finite measure with bounded Riesz potentials has a
Hölder logarithmic potential. -/
theorem log_potential_integrable_and_holder {μ : Measure ℂ} [IsFiniteMeasure μ]
    [NullSingletonClass μ] {K M : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z : ℂ, ∫⁻ w, ENNReal.ofReal (‖z - w‖ ^ (-(1 / 2 : ℝ))) ∂μ ≤
      ENNReal.ofReal K) (hsupp : ∀ᵐ w ∂μ, ‖w‖ ≤ M) :
    (∀ z : ℂ, Integrable (fun w => Real.log ‖z - w‖) μ) ∧
    HolderOnWith ⟨4 * K, by positivity⟩ ⟨1 / 2, by norm_num⟩
      (fun z => ∫ w, Real.log ‖z - w‖ ∂μ) univ := by
  have hi : ∀ z : ℂ, Integrable (fun w => ‖z - w‖ ^ (-(1 / 2 : ℝ))) μ ∧
      (∫ w, ‖z - w‖ ^ (-(1 / 2 : ℝ)) ∂μ) ≤ K :=
    fun z => integrable_norm_sub_rpow_neg hK (hbound z)
  have hlog : ∀ z : ℂ, Integrable (fun w => Real.log ‖z - w‖) μ := by
    intro z
    let A := (1 / 2 : ℝ)⁻¹ * (‖z‖ + M + 1) ^ (1 / 2 : ℝ)
    have hdom : Integrable (fun w => A * (‖z - w‖ ^ (-(1 / 2 : ℝ)) + 1)) μ :=
      ((hi z).1.add (integrable_const 1)).const_mul A
    have hmeas : AEStronglyMeasurable (fun w : ℂ => Real.log ‖z - w‖) μ :=
      (Real.measurable_log.comp ((continuous_const.sub continuous_id).norm.measurable)).aestronglyMeasurable
    apply hdom.mono' hmeas
    filter_upwards [hsupp] with w hw
    have hd : ‖z - w‖ ≤ ‖z‖ + M := by
      have hh := norm_sub_le z w
      linarith
    simpa only [Real.norm_eq_abs, A] using
      abs_log_le_rpow_of_bounded (norm_nonneg (z - w)) hd (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1)
  refine ⟨hlog, holderOnWith_of_dist_le ?_⟩
  intro z _ z' _
  have hne : ∀ᵐ w ∂μ, w ≠ z ∧ w ≠ z' := by
    have hz : ∀ᵐ w ∂μ, w ≠ z := ae_iff.2 (by simp)
    have hz' : ∀ᵐ w ∂μ, w ≠ z' := ae_iff.2 (by simp)
    filter_upwards [hz, hz'] with w hw hw'
    exact ⟨hw, hw'⟩
  have hdom : Integrable (fun w => (1 / 2 : ℝ)⁻¹ * ‖z - z'‖ ^ (1 / 2 : ℝ) *
      (‖z - w‖ ^ (-(1 / 2 : ℝ)) + ‖z' - w‖ ^ (-(1 / 2 : ℝ)))) μ :=
    ((hi z).1.add (hi z').1).const_mul _
  have hp : 0 ≤ (1 / 2 : ℝ)⁻¹ * ‖z - z'‖ ^ (1 / 2 : ℝ) := by positivity
  have hpoint : ∀ᵐ w ∂μ, ‖Real.log ‖z - w‖ - Real.log ‖z' - w‖‖ ≤
      (1 / 2 : ℝ)⁻¹ * ‖z - z'‖ ^ (1 / 2 : ℝ) *
        (‖z - w‖ ^ (-(1 / 2 : ℝ)) + ‖z' - w‖ ^ (-(1 / 2 : ℝ))) := by
    filter_upwards [hne] with w hw
    have ha : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hw.1))
    have hb : 0 < ‖z' - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hw.2))
    have hd : |‖z - w‖ - ‖z' - w‖| ≤ ‖z - z'‖ := by
      simpa using abs_norm_sub_norm_le (z - w) (z' - w)
    have hr := Real.rpow_le_rpow (abs_nonneg _) hd (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [Real.norm_eq_abs]
    exact (abs_log_sub_log_le ha hb (by norm_num) (by norm_num)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr (by positivity)) (by positivity))
  rw [Real.dist_eq, ← integral_sub (hlog z) (hlog z'), ← Real.norm_eq_abs]
  calc ‖∫ w, (Real.log ‖z - w‖ - Real.log ‖z' - w‖) ∂μ‖
      ≤ ∫ w, ((1 / 2 : ℝ)⁻¹ * ‖z - z'‖ ^ (1 / 2 : ℝ) *
          (‖z - w‖ ^ (-(1 / 2 : ℝ)) + ‖z' - w‖ ^ (-(1 / 2 : ℝ)))) ∂μ :=
        norm_integral_le_of_norm_le hdom hpoint
    _ = ((1 / 2 : ℝ)⁻¹ * ‖z - z'‖ ^ (1 / 2 : ℝ)) *
        ((∫ w, ‖z - w‖ ^ (-(1 / 2 : ℝ)) ∂μ) +
          (∫ w, ‖z' - w‖ ^ (-(1 / 2 : ℝ)) ∂μ)) := by
        rw [integral_const_mul, integral_add (hi z).1 (hi z').1]
    _ ≤ ((1 / 2 : ℝ)⁻¹ * ‖z - z'‖ ^ (1 / 2 : ℝ)) * (K + K) :=
      mul_le_mul_of_nonneg_left (add_le_add (hi z).2 (hi z').2) hp
    _ = (⟨4 * K, by positivity⟩ : ℝ≥0) * dist z z' ^ ((⟨1 / 2, by norm_num⟩ : ℝ≥0) : ℝ) := by
      simp only [dist_eq_norm]
      ring

/-- For every start, one event gives finite and Hölder continuous logarithmic
potentials of the actual stopped occupation measures for all bounded domains. -/
theorem planarBrownianMotion_stopped_log_potential_integrable_and_holder (x : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ D : Set ℂ, Bornology.IsBounded D →
      (∀ z : ℂ, Integrable (fun w => Real.log ‖z - w‖) (stoppedBrownianOccupation D b)) ∧
      ∃ C : ℝ≥0, HolderOnWith C (1 / 2 : ℝ≥0)
        (fun z => ∫ w, Real.log ‖z - w‖ ∂(stoppedBrownianOccupation D b)) univ := by
  have hballs : ∀ᵐ b ∂(planarBrownianMotion x), ∀ n : ℕ,
      ContinuousPath.exitTime (ball x (n : ℝ)) b < ∞ := by
    simp only [ae_all_iff]
    exact fun n => Section6.ae_planarBrownianMotion_exitTime_ball_lt_top x n
  filter_upwards [planarBrownianMotion_stopped_uniform_riesz_potential x,
    planarBrownianMotion_stoppedOccupation_nullSingleton_all_domains x, hballs] with b hriesz hatom hball D hD
  obtain ⟨R, hR⟩ := hD.subset_ball x
  obtain ⟨n, hn⟩ := exists_nat_ge R
  have hsub : D ⊆ ball x (n : ℝ) := hR.trans (ball_subset_ball hn)
  have hfin : ContinuousPath.exitTime D b < ∞ :=
    lt_of_le_of_lt (ContinuousPath.exitTime_mono hsub b) (hball n)
  let μ := stoppedBrownianOccupation D b
  have : IsFiniteMeasure μ := ⟨by
    rw [show μ = stoppedBrownianOccupation D b from rfl, stoppedBrownianOccupation_univ D b hfin.ne]
    exact hfin⟩
  have : NullSingletonClass μ := hatom D hD
  obtain ⟨K, hK, hbound⟩ := hriesz D hD
  have hf : Continuous (fun t : ℝ => b t.toNNReal) := b.continuous.comp continuous_real_toNNReal
  obtain ⟨M, hM, hMsub⟩ := ((isCompact_Icc.image hf).isBounded).subset_ball_lt 0 (0 : ℂ)
  have hsupp : ∀ᵐ w ∂μ, ‖w‖ ≤ M := by
    change ∀ᵐ w ∂(Measure.map (fun t : ℝ => b t.toNNReal)
      (volume.restrict {t : ℝ | 0 < t ∧ ((t.toNNReal : ℝ≥0) : ℝ≥0∞) <
        ContinuousPath.exitTime D b})), ‖w‖ ≤ M
    apply (ae_map_iff hf.measurable.aemeasurable (show MeasurableSet {w : ℂ | ‖w‖ ≤ M} by
      exact measurableSet_le continuous_norm.measurable measurable_const)).2
    have heq : {t : ℝ | 0 < t ∧ ((t.toNNReal : ℝ≥0) : ℝ≥0∞) <
        ContinuousPath.exitTime D b} = Ioo 0 (ContinuousPath.exitTime D b).toReal := by
      simpa [Set.inter_def, and_comm] using
        ContinuousPath.survivalSet_ne_top (ContinuousPath.exitTime D b) hfin.ne
    rw [heq]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht' : t ∈ Icc (0 : ℝ) (ContinuousPath.exitTime D b).toReal := ⟨ht.1.le, ht.2.le⟩
    have hm := hMsub ⟨t, ht', rfl⟩
    have : ‖b t.toNNReal‖ < M := by simpa [mem_ball, dist_eq_norm] using hm
    exact this.le
  obtain ⟨hI, hH⟩ := log_potential_integrable_and_holder hK hbound hsupp
  exact ⟨hI, ⟨⟨4 * K, by positivity⟩, hH⟩⟩

/-- The Newtonian representative is integrable at every center and its stopped
occupation potential is continuous, simultaneously for all bounded domains. -/
theorem planarBrownianMotion_stopped_newton_potential_continuous (x : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ D : Set ℂ, Bornology.IsBounded D →
      (∀ z : ℂ, Integrable (newtonKernel z) (stoppedBrownianOccupation D b)) ∧
      Continuous (fun z => ∫ w, newtonKernel z w ∂(stoppedBrownianOccupation D b)) := by
  filter_upwards [planarBrownianMotion_stopped_log_potential_integrable_and_holder x] with b hb D hD
  obtain ⟨hi, C, hH⟩ := hb D hD
  have hc : Continuous (fun z => ∫ w, Real.log ‖z - w‖ ∂(stoppedBrownianOccupation D b)) :=
    continuousOn_univ.mp (hH.continuousOn (by norm_num))
  constructor
  · intro z
    change Integrable (fun w => -(2 * Real.pi)⁻¹ * Real.log ‖z - w‖) _
    exact (hi z).const_mul (-(2 * Real.pi)⁻¹)
  · simpa only [newtonKernel, integral_const_mul] using hc.const_mul (-(2 * Real.pi)⁻¹)

end HarmonicBalls
