import HarmonicBalls.Proofs.Potential.BrownianAllHorizonBallOccupation
import HarmonicBalls.Proofs.Potential.BrownianSharpLogOccupationEvent

/-! # Sharp Brownian occupation bounds on finite horizons

Brownian scaling transfers the logarithmic unit-time occupation bound to all finite horizons.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal
open HarmonicBalls.Section6

namespace HarmonicBalls

/-- The logarithmic occupation bound transfers under Brownian scaling. -/
theorem scaled_occupation_log_bound (x : ℂ) (b : ContinuousPath ℂ) (c : ℝ≥0)
    (hc : 1 ≤ c) (C : ℝ) (hC : 0 < C) (r₀ : ℝ) (hr₀ : 0 < r₀)
    (h : ∀ (z : ℂ) (r : ℝ), 0 < r → r < r₀ →
      volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
        ‖scaledCenteredPlanarPath x c b (Real.toNNReal t) - z‖ < r} ≤
          ENNReal.ofReal (C * r ^ 2 * (Real.log (1 / r)) ^ 2)) :
    ∃ D : ℝ, 0 < D ∧ ∃ R : ℝ, 0 < R ∧ ∀ (z : ℂ) (r : ℝ), 0 < r → r < R →
      volume {t : ℝ | t ∈ Icc (0 : ℝ) c ∧ ‖b (Real.toNNReal t) - z‖ < r} ≤
        ENNReal.ofReal (D * r ^ 2 * (Real.log (1 / r)) ^ 2) := by
  let k : ℝ := (Real.sqrt c)⁻¹
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hcpos : (0 : ℝ) < c := by linarith
  have hs : 1 ≤ Real.sqrt c := (Real.le_sqrt (by norm_num) hcpos.le).2 (by nlinarith)
  have hk : 0 < k := inv_pos.mpr (Real.sqrt_pos.2 hcpos)
  have hk1 : k ≤ 1 := by dsimp [k]; exact (inv_le_one₀ (Real.sqrt_pos.2 hcpos)).2 hs
  refine ⟨4 * c * C, by positivity, min r₀ k, lt_min hr₀ hk, ?_⟩
  intro z r hr hrsmall
  have hrsmall : r < r₀ ∧ r < k := lt_min_iff.mp hrsmall
  let S : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧
        ‖scaledCenteredPlanarPath x c b (Real.toNNReal t) - k • (z - x)‖ < k * r}
  have hS := h (k • (z - x)) (k * r) (mul_pos hk hr) (by nlinarith [hrsmall.1])
  have hset : {t : ℝ | t ∈ Icc (0 : ℝ) c ∧ ‖b (Real.toNNReal t) - z‖ < r} =
      ((fun t : ℝ => (c : ℝ)⁻¹ * t) ⁻¹' S) := by
    ext t
    simp only [mem_ofPred_eq, mem_preimage, mem_Icc, S]
    have htime : Real.toNNReal ((c : ℝ)⁻¹ * t) = c⁻¹ * Real.toNNReal t := by
      rw [Real.toNNReal_mul (inv_nonneg.mpr hcpos.le)]
      congr 1
      rw [← NNReal.coe_inv]
      exact Real.toNNReal_coe
    have hnorm : ‖scaledCenteredPlanarPath x c b (Real.toNNReal ((c : ℝ)⁻¹ * t)) -
        k • (z - x)‖ = k * ‖b (Real.toNNReal t) - z‖ := by
      rw [htime]
      simp only [scaledCenteredPlanarPath, ContinuousMap.coe_mk]
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (show (0 : ℝ≥0) < c by exact_mod_cast hcpos)), one_mul]
      change ‖k • (b (Real.toNNReal t) - x) - k • (z - x)‖ = _
      rw [← smul_sub, show b (Real.toNNReal t) - x - (z - x) = b (Real.toNNReal t) - z by abel,
        norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    rw [hnorm, mul_lt_mul_iff_of_pos_left hk]
    constructor <;> rintro ⟨⟨h0, h1⟩, hball⟩
    · exact ⟨⟨mul_nonneg (inv_nonneg.mpr hcpos.le) h0,
        (inv_mul_le_one₀ hcpos).2 h1⟩, hball⟩
    · exact ⟨⟨(mul_nonneg_iff_of_pos_left (inv_pos.mpr hcpos)).1 h0,
        (inv_mul_le_one₀ hcpos).1 h1⟩, hball⟩
  rw [hset, Real.volume_preimage_mul_left (inv_ne_zero hcpos.ne'), inv_inv, abs_of_pos hcpos]
  have hlogr : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_div hr |>.2 (by linarith [hrsmall.2]))
  have hlogk : 0 ≤ Real.log (1 / k) := Real.log_nonneg (one_le_div hk |>.2 hk1)
  have hlogle : Real.log (1 / k) ≤ Real.log (1 / r) :=
    Real.log_le_log (by positivity) (by gcongr; linarith [hrsmall.2])
  have hlogeq : Real.log (1 / (k * r)) = Real.log (1 / k) + Real.log (1 / r) := by
    rw [show 1 / (k * r) = (1 / k) * (1 / r) by field_simp, Real.log_mul (by positivity) (by positivity)]
  have hlogsq : (Real.log (1 / (k * r))) ^ 2 ≤ 4 * (Real.log (1 / r)) ^ 2 := by
    rw [hlogeq]
    nlinarith
  have hrsq : (k * r) ^ 2 ≤ r ^ 2 := by
    gcongr
    nlinarith
  calc
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (C * (k * r) ^ 2 * (Real.log (1 / (k * r))) ^ 2) := by
      simpa only [S, mul_comm] using (mul_le_mul_left hS (ENNReal.ofReal c))
    _ ≤ ENNReal.ofReal ((4 * c * C) * r ^ 2 * (Real.log (1 / r)) ^ 2) := by
      rw [← ENNReal.ofReal_mul hcpos.le]
      apply ENNReal.ofReal_le_ofReal
      calc
        c * (C * (k * r) ^ 2 * (Real.log (1 / (k * r))) ^ 2) ≤
            c * (C * r ^ 2 * (4 * (Real.log (1 / r)) ^ 2)) := by gcongr
        _ = _ := by ring

/-- Almost surely, the sharp logarithmic occupation bound holds on every finite horizon. -/
theorem planarBrownianMotion_uniform_ball_occupation_log_all_horizons (x : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ T : ℝ, 0 ≤ T →
      ∃ C : ℝ, 0 < C ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
        ∀ (z : ℂ) (r : ℝ), 0 < r → r < r₀ →
          volume {t : ℝ | t ∈ Icc (0 : ℝ) T ∧ ‖b (Real.toNNReal t) - z‖ < r} ≤
            ENNReal.ofReal (C * r ^ 2 * (Real.log (1 / r)) ^ 2) := by
  have hn : ∀ n : ℕ, ∀ᵐ b ∂(planarBrownianMotion x),
      ∃ C : ℝ, 0 < C ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
        ∀ (z : ℂ) (r : ℝ), 0 < r → r < r₀ →
          volume {t : ℝ | t ∈ Icc (0 : ℝ) (n + 1 : ℕ) ∧
            ‖b (Real.toNNReal t) - z‖ < r} ≤
              ENNReal.ofReal (C * r ^ 2 * (Real.log (1 / r)) ^ 2) := by
    intro n
    let c : ℝ≥0 := n + 1
    have hc : 1 ≤ c := by simp [c]
    have hscale := planarBrownianMotion_map_scaledCenteredPlanarPath x
      (c := c) (ne_of_gt (lt_of_lt_of_le zero_lt_one hc))
    have ha := planarBrownianMotion_uniform_ball_occupation_log_real_time 0
    rw [← hscale] at ha
    have hb := ae_of_ae_map (continuous_scaledCenteredPlanarPath x c).measurable.aemeasurable ha
    filter_upwards [hb] with b hb
    obtain ⟨C, hC, r₀, hr₀, hbound⟩ := hb
    simpa [c] using scaled_occupation_log_bound x b c hc C hC r₀ hr₀ hbound
  filter_upwards [ae_all_iff.mpr hn] with b hb T _
  obtain ⟨n, hn⟩ := exists_nat_gt T
  obtain ⟨C, hC, r₀, hr₀, hbound⟩ := hb n
  refine ⟨C, hC, r₀, hr₀, ?_⟩
  intro z r hr hrsmall
  apply le_trans (measure_mono ?_) (hbound z r hr hrsmall)
  intro t ht
  exact ⟨⟨ht.1.1, ht.1.2.trans (by push_cast; linarith)⟩, ht.2⟩

/-- The all-horizon bound for the pushforward of restricted real-time volume. -/
theorem planarBrownianMotion_uniform_ball_occupation_log_all_horizons_mapped (x : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ T : ℝ, 0 ≤ T →
      ∃ C : ℝ, 0 < C ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
        ∀ (z : ℂ) (r : ℝ), 0 < r → r < r₀ →
          Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) T))
            {t | ‖b t - z‖ < r} ≤ ENNReal.ofReal (C * r ^ 2 * (Real.log (1 / r)) ^ 2) := by
  filter_upwards [planarBrownianMotion_uniform_ball_occupation_log_all_horizons x] with b hb T hT
  obtain ⟨C, hC, r₀, hr₀, hbound⟩ := hb T hT
  refine ⟨C, hC, r₀, hr₀, ?_⟩
  intro z r hr hrsmall
  have hm : MeasurableSet {t : ℝ≥0 | ‖b t - z‖ < r} := by
    apply isOpen_lt _ continuous_const |>.measurableSet
    fun_prop
  rw [Measure.map_apply continuous_real_toNNReal.measurable hm,
    Measure.restrict_apply (continuous_real_toNNReal.measurable hm)]
  convert hbound z r hr hrsmall using 1
  congr 1
  ext t
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
  tauto

end HarmonicBalls
