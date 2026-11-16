import HarmonicBalls.Proofs.Potential.BrownianUniformBallOccupation
import HarmonicBalls.Proofs.Potential.BrownianOccupationRieszEnergy

/-! # Singular Brownian occupation

Subcritical inverse-power weights are integrable along planar Brownian paths.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- The expected unit-time occupation of a ball has subcritical polynomial growth. -/
theorem planarBrownianMotion_unit_single_ball_occupation_le (x z : ℂ) {d : ℝ}
    (hd0 : 0 < d) (hd2 : d < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      (∫⁻ b, ∫⁻ t : ℝ≥0,
        (if ‖b t - z‖ < r then 1 else 0 : ℝ≥0∞) ∂ν
          ∂(planarBrownianMotion x)) ≤ ENNReal.ofReal (C * r ^ d) := by
  let q : ℝ := d / 2
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hqd : 2 * q = d := by dsimp [q]; ring
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let K : ℝ≥0∞ := ∫⁻ t in Icc (0 : ℝ) 1, ‖t‖ₑ ^ (-q)
  have hK : K < ∞ := by
    have hsub : Icc (0 : ℝ) 1 ⊆ ball (0 : ℝ) 2 := by
      intro t ht
      simp only [mem_ball, Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    have hb : (∫⁻ t in ball (0 : ℝ) 2, ‖t‖ₑ ^ (-q)) < ∞ := by
      convert (show (∫⁻ t in ball (0 : ℝ) 2, ‖t - (0 : ℝ)‖ₑ ^ (-q)) < ∞ from ?_) using 1
      · simp
      rw [LatticeProb.PegdenSmart.lintegral_ball_enorm_sub_rpow volume 0 (by norm_num : (0 : ℝ) < 2)]
      apply ENNReal.mul_lt_top
      · apply ENNReal.rpow_lt_top_of_nonneg
        · simp only [Module.finrank_self, Nat.cast_one]; linarith
        · exact ENNReal.ofReal_ne_top
      · apply LatticeProb.PegdenSmart.lintegral_ball_enorm_rpow_lt_top volume
        simp only [Module.finrank_self, Nat.cast_one]; linarith
    exact (lintegral_mono_set hsub).trans_lt hb
  let C : ℝ := (2 / Real.pi) ^ q * (K.toReal + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro r hr
  have hν : NullSingletonClass ν := by
    constructor
    intro t
    dsimp [ν]
    rw [Measure.map_apply continuous_real_toNNReal.measurable (measurableSet_singleton t),
      Measure.restrict_apply (continuous_real_toNNReal.measurable (measurableSet_singleton t))]
    apply measure_mono_null _ (measure_singleton (t : ℝ))
    intro a ha
    have ht := congrArg (fun v : ℝ≥0 => (v : ℝ)) ha.1
    have ha0 : 0 ≤ a := ha.2.1
    simpa [Real.toNNReal_of_nonneg ha0] using ht
  let : NullSingletonClass ν := hν
  let E : Set (ContinuousPath ℂ × ℝ≥0) := {p | ‖p.1 p.2 - z‖ < r}
  have hE : MeasurableSet E := by
    apply isOpen_lt _ continuous_const |>.measurableSet
    fun_prop
  have hswap : (∫⁻ b, ∫⁻ t : ℝ≥0, (if ‖b t - z‖ < r then 1 else 0 : ℝ≥0∞) ∂ν
      ∂(planarBrownianMotion x)) = ∫⁻ t : ℝ≥0,
        planarBrownianMotion x {b | ‖b t - z‖ < r} ∂ν := by
    let F : ContinuousPath ℂ × ℝ≥0 → ℝ≥0∞ := E.indicator 1
    have hF : Measurable F := measurable_const.indicator hE
    calc
      _ = ∫⁻ b, ∫⁻ t, F (b,t) ∂ν ∂(planarBrownianMotion x) := by simp [F, E, Set.indicator_apply]
      _ = ∫⁻ t, ∫⁻ b, F (b,t) ∂(planarBrownianMotion x) ∂ν := lintegral_lintegral_swap hF.aemeasurable
      _ = _ := by
        congr 1; funext t
        have hm : MeasurableSet {b : ContinuousPath ℂ | ‖b t - z‖ < r} := by
          apply isOpen_lt _ continuous_const |>.measurableSet
          fun_prop
        convert lintegral_indicator_one hm using 1; simp [F, E, Set.indicator_apply]
  have hbound (t : ℝ≥0) (ht : t ≠ 0) :
      planarBrownianMotion x {b | ‖b t - z‖ < r} ≤
        ENNReal.ofReal ((2 / Real.pi) ^ q * r ^ d * |(t : ℝ)| ^ (-q)) := by
    have heq : planarBrownianMotion x {b | ‖b t - z‖ < r} =
        planarBrownianMotion x {b | ‖b t - b 0 - (z - x)‖ < r} := by
      apply measure_congr
      filter_upwards [ae_planarBrownianMotion_eval_zero x] with b hb
      simp only [hb]
      congr 1
      congr 1
      abel
    rw [heq]
    simpa [hqd] using planarBrownianMotion_increment_smallBall_rpow_le_uniform_center x (z - x) ht hr hq0 hq1
  have hkernel : (∫⁻ t : ℝ≥0, ENNReal.ofReal (|(t : ℝ)| ^ (-q)) ∂ν) ≤ K := by
    rw [show ν = Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)) from rfl,
      lintegral_map (by fun_prop) continuous_real_toNNReal.measurable]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with t ht ht0
    have hp : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    simp only [Real.toNNReal_of_nonneg ht.1]
    change ENNReal.ofReal (‖t‖ ^ (-q)) ≤ ‖t‖ₑ ^ (-q)
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_pos hp]
  have hA : 0 ≤ (2 / Real.pi) ^ q * r ^ d := by positivity
  have hKbound : K ≤ ENNReal.ofReal (K.toReal + 1) := by
    calc
      K = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hK.ne).symm
      _ ≤ ENNReal.ofReal (K.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  change (∫⁻ b, ∫⁻ t : ℝ≥0, (if ‖b t - z‖ < r then 1 else 0 : ℝ≥0∞) ∂ν
    ∂(planarBrownianMotion x)) ≤ ENNReal.ofReal (C * r ^ d)
  rw [hswap]
  calc
    _ ≤ ∫⁻ t : ℝ≥0, ENNReal.ofReal ((2 / Real.pi) ^ q * r ^ d * |(t : ℝ)| ^ (-q)) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [ν.ae_ne 0] with t ht
      exact hbound t ht
    _ = ENNReal.ofReal ((2 / Real.pi) ^ q * r ^ d) *
        (∫⁻ t : ℝ≥0, ENNReal.ofReal (|(t : ℝ)| ^ (-q)) ∂ν) := by
      simp_rw [ENNReal.ofReal_mul hA]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal ((2 / Real.pi) ^ q * r ^ d) * ENNReal.ofReal (K.toReal + 1) := by gcongr; exact hkernel.trans hKbound
    _ = ENNReal.ofReal (C * r ^ d) := by
      rw [← ENNReal.ofReal_mul hA]
      congr 1
      dsimp [C]
      ring

/-- The expected unit-time inverse-power occupation is finite below dimension two. -/
theorem planarBrownianMotion_unit_singular_occupation_lt_top (x z : ℂ) {β : ℝ}
    (hβ0 : 0 < β) (hβ2 : β < 2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    (∫⁻ b, ∫⁻ t : ℝ≥0, (ENNReal.ofReal ‖b t - z‖) ^ (-β) ∂ν
      ∂(planarBrownianMotion x)) < ∞ := by
  let d : ℝ := (β + 2) / 2
  have hd0 : 0 < d := by dsimp [d]; linarith
  have hβd : β < d := by dsimp [d]; linarith
  have hd2 : d < 2 := by dsimp [d]; linarith
  obtain ⟨C, hC, hbound⟩ := planarBrownianMotion_unit_single_ball_occupation_le x z hd0 hd2
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let f : ContinuousPath ℂ × ℝ≥0 → ℂ := fun p => p.1 p.2 - z
  have hf : Measurable f := by dsimp [f]; fun_prop
  let ρ := (planarBrownianMotion x).prod ν
  let μ := ρ.map f
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  have hμ : μ univ ≤ ENNReal.ofReal 1 := by
    rw [show μ = ρ.map f from rfl, Measure.map_apply hf MeasurableSet.univ]
    simp only [preimage_univ, ENNReal.ofReal_one]
    change (planarBrownianMotion x).prod ν univ ≤ 1
    rw [← univ_prod_univ, Measure.prod_prod, hν]
    simp
  let A : ℝ := C * 2 ^ d
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hball : ∀ r : ℝ, 0 < r → μ (closedBall 0 r) ≤ ENNReal.ofReal (A * r ^ d) := by
    intro r hr
    have hsub : closedBall (0 : ℂ) r ⊆ ball 0 (2 * r) := by
      intro w hw
      rw [mem_closedBall] at hw
      rw [mem_ball]
      linarith
    calc
      μ (closedBall 0 r) ≤ μ (ball 0 (2 * r)) := measure_mono hsub
      _ = (∫⁻ b, ∫⁻ t : ℝ≥0,
          (if ‖b t - z‖ < 2 * r then 1 else 0 : ℝ≥0∞) ∂ν
            ∂(planarBrownianMotion x)) := by
        rw [show μ = ρ.map f from rfl, Measure.map_apply hf isOpen_ball.measurableSet,
          Measure.prod_apply (hf isOpen_ball.measurableSet)]
        congr 1; funext b
        have hs : MeasurableSet {t : ℝ≥0 | ‖b t - z‖ < 2 * r} := by
          apply isOpen_lt _ continuous_const |>.measurableSet
          fun_prop
        have hset : Set.preimage (Prod.mk b) (Set.preimage f (ball 0 (2 * r))) =
            {t : ℝ≥0 | ‖b t - z‖ < 2 * r} := by
          ext t
          simp [f, mem_ball, dist_zero_right]
        rw [hset]
        simpa [Set.indicator_apply] using (lintegral_indicator_one hs (μ := ν)).symm
      _ ≤ ENNReal.ofReal (C * (2 * r) ^ d) := hbound _ (by linarith)
      _ = ENNReal.ofReal (A * r ^ d) := by
        rw [Real.mul_rpow (by positivity) (le_of_lt hr)]
        congr 1
        dsimp [A]
        ring
  have henergy := lintegral_enorm_rpow_neg_lt_top_of_ball_le hβ0 hβd
    (by norm_num : (0 : ℝ) ≤ 1) hA hμ hball
  have hg : Measurable (fun w : ℂ => (ENNReal.ofReal ‖w‖) ^ (-β)) := by fun_prop
  rw [show μ = ρ.map f from rfl, lintegral_map hg hf] at henergy
  change (∫⁻ a, ((fun w : ℂ => (ENNReal.ofReal ‖w‖) ^ (-β)) ∘ f) a
    ∂((planarBrownianMotion x).prod ν)) < ∞ at henergy
  rw [lintegral_prod _ (hg.comp hf).aemeasurable] at henergy
  exact henergy

/-- The unit-time inverse-power occupation is almost surely finite below dimension two. -/
theorem planarBrownianMotion_ae_unit_singular_occupation_lt_top (x z : ℂ) {β : ℝ}
    (hβ0 : 0 < β) (hβ2 : β < 2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x),
      (∫⁻ t : ℝ≥0, (ENNReal.ofReal ‖b t - z‖) ^ (-β) ∂ν) < ∞ := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hf : Measurable (fun p : ContinuousPath ℂ × ℝ≥0 =>
      (ENNReal.ofReal ‖p.1 p.2 - z‖) ^ (-β)) := by fun_prop
  exact ae_lt_top (Measurable.lintegral_prod_right hf)
    (planarBrownianMotion_unit_singular_occupation_lt_top x z hβ0 hβ2).ne

end HarmonicBalls
