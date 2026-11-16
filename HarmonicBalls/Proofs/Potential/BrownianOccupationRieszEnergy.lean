import HarmonicBalls.Proofs.Potential.BrownianPairOccupationBound
import HarmonicBalls.Proofs.Potential.GreenPotentialHolder

/-! # Brownian occupation energy

The unit-time occupation measure of planar Brownian motion has finite subcritical Riesz energy.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- A measure with polynomial growth has finite subcritical inverse-power moment. -/
theorem lintegral_enorm_rpow_neg_lt_top_of_ball_le {μ : Measure ℂ} {m A α β : ℝ}
    (hα : 0 < α) (hαβ : α < β) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hμ : μ univ ≤ ENNReal.ofReal m)
    (hball : ∀ r, 0 < r → μ (closedBall 0 r) ≤ ENNReal.ofReal (A * r ^ β)) :
    (∫⁻ z, (ENNReal.ofReal ‖z‖) ^ (-α) ∂μ) < ∞ := by
  have hβ : 0 < β := hα.trans hαβ
  have hzero : μ {(0 : ℂ)} = 0 := measure_singleton_eq_zero_of_le_rpow hβ hball
  have hae : ∀ᵐ z ∂μ, z ≠ 0 := by
    simpa using (measure_eq_zero_iff_ae_notMem.mp hzero)
  have heq : (∫⁻ z, (ENNReal.ofReal ‖z‖) ^ (-α) ∂μ) =
      ∫⁻ z, ENNReal.ofReal (‖(0 : ℂ) - z‖ ^ (-α)) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hae] with z hz
    rw [ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr hz)]
    simp
  rw [heq]
  exact (lintegral_norm_sub_rpow_neg_le hα hαβ hm hA hμ hball).trans_lt
    ENNReal.ofReal_lt_top

/-- The expected unit-time Riesz energy is finite at every subcritical exponent. -/
theorem planarBrownianMotion_unit_occupation_riesz_energy_lt_top (x : ℂ) {β : ℝ}
    (hβ0 : 0 < β) (hβ2 : β < 2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    (∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0,
      (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-β) ∂(ν.prod ν)
        ∂(planarBrownianMotion x)) < ∞ := by
  let d : ℝ := (β + 2) / 2
  have hd0 : 0 < d := by dsimp [d]; linarith
  have hβd : β < d := by dsimp [d]; linarith
  have hd2 : d < 2 := by dsimp [d]; linarith
  obtain ⟨C, hC, hbound⟩ := planarBrownianMotion_unit_pair_occupation_le x hd0 hd2
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let f : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0) → ℂ := fun q => q.1 q.2.1 - q.1 q.2.2
  have hf : Measurable f := by dsimp [f]; fun_prop
  let ρ := (planarBrownianMotion x).prod (ν.prod ν)
  let μ := ρ.map f
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  have hμ : μ univ ≤ ENNReal.ofReal 1 := by
    rw [show μ = ρ.map f from rfl, Measure.map_apply hf MeasurableSet.univ]
    simp only [preimage_univ, ENNReal.ofReal_one]
    change (planarBrownianMotion x).prod (ν.prod ν) univ ≤ 1
    rw [← univ_prod_univ, Measure.prod_prod, ← univ_prod_univ, Measure.prod_prod, hν]
    simp
  let A : ℝ := C * 2 ^ d
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hball : ∀ r : ℝ, 0 < r → μ (closedBall 0 r) ≤ ENNReal.ofReal (A * r ^ d) := by
    intro r hr
    have hsub : closedBall (0 : ℂ) r ⊆ ball 0 (2 * r) := by
      intro z hz
      rw [mem_closedBall] at hz
      rw [mem_ball]
      linarith
    calc
      μ (closedBall 0 r) ≤ μ (ball 0 (2 * r)) := measure_mono hsub
      _ = (∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0,
          (if ‖b p.1 - b p.2‖ < 2 * r then 1 else 0 : ℝ≥0∞) ∂(ν.prod ν)
            ∂(planarBrownianMotion x)) := by
        rw [show μ = ρ.map f from rfl, Measure.map_apply hf isOpen_ball.measurableSet,
          Measure.prod_apply (hf isOpen_ball.measurableSet)]
        congr 1; funext b
        have hs : MeasurableSet {p : ℝ≥0 × ℝ≥0 | ‖b p.1 - b p.2‖ < 2 * r} := by
          apply isOpen_lt _ continuous_const |>.measurableSet
          fun_prop
        have hset : Set.preimage (Prod.mk b) (Set.preimage f (ball 0 (2 * r))) =
            {p : ℝ≥0 × ℝ≥0 | ‖b p.1 - b p.2‖ < 2 * r} := by
          ext p
          simp [f, mem_ball, dist_zero_right]
        rw [hset]
        simpa [Set.indicator_apply] using (lintegral_indicator_one hs (μ := ν.prod ν)).symm
      _ ≤ ENNReal.ofReal (C * (2 * r) ^ d) := hbound _ (by linarith)
      _ = ENNReal.ofReal (A * r ^ d) := by
        rw [Real.mul_rpow (by positivity) (le_of_lt hr)]
        congr 1
        dsimp [A]
        ring
  have henergy := lintegral_enorm_rpow_neg_lt_top_of_ball_le hβ0 hβd
    (by norm_num : (0 : ℝ) ≤ 1) hA hμ hball
  have hg : Measurable (fun z : ℂ => (ENNReal.ofReal ‖z‖) ^ (-β)) := by fun_prop
  rw [show μ = ρ.map f from rfl, lintegral_map hg hf] at henergy
  change (∫⁻ a, ((fun z : ℂ => (ENNReal.ofReal ‖z‖) ^ (-β)) ∘ f) a
    ∂((planarBrownianMotion x).prod (ν.prod ν))) < ∞ at henergy
  rw [lintegral_prod _ (hg.comp hf).aemeasurable] at henergy
  exact henergy

/-- The unit-time occupation energy is almost surely finite. -/
theorem planarBrownianMotion_ae_unit_occupation_riesz_energy_lt_top (x : ℂ) {β : ℝ}
    (hβ0 : 0 < β) (hβ2 : β < 2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x),
      (∫⁻ p : ℝ≥0 × ℝ≥0, (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-β)
        ∂(ν.prod ν)) < ∞ := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hf : Measurable (fun q : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0) =>
      (ENNReal.ofReal ‖q.1 q.2.1 - q.1 q.2.2‖) ^ (-β)) := by fun_prop
  exact ae_lt_top (Measurable.lintegral_prod_right hf)
    (planarBrownianMotion_unit_occupation_riesz_energy_lt_top x hβ0 hβ2).ne

end HarmonicBalls
