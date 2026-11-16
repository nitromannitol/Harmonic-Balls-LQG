import HarmonicBalls.Proofs.Potential.BrownianUniformBallOccupation

/-! # Brownian occupation on finite horizons

Brownian scaling extends uniform unit-time occupation estimates to every finite horizon.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal
open HarmonicBalls.Section6

namespace HarmonicBalls

/-- A unit-time occupation bound transfers under Brownian scaling. -/
theorem scaled_occupation_bound (x : ℂ) (b : ContinuousPath ℂ) (c : ℝ≥0)
    (hc : 1 ≤ c) {d : ℝ} (hd : 0 < d) (C : ℝ) (hC : 0 < C)
    (h : ∀ (z : ℂ) (r : ℝ), 0 < r → r ≤ 1 →
      volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
        ‖scaledCenteredPlanarPath x c b (Real.toNNReal t) - z‖ < r} ≤
          ENNReal.ofReal (C * r ^ d)) :
    ∃ D : ℝ, 0 < D ∧ ∀ (z : ℂ) (r : ℝ), 0 < r → r ≤ 1 →
      volume {t : ℝ | t ∈ Icc (0 : ℝ) c ∧ ‖b (Real.toNNReal t) - z‖ < r} ≤
        ENNReal.ofReal (D * r ^ d) := by
  let k : ℝ := (Real.sqrt c)⁻¹
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hcpos : (0 : ℝ) < c := by linarith
  have hs : 1 ≤ Real.sqrt c := (Real.le_sqrt (by norm_num) hcpos.le).2 (by nlinarith)
  have hk : 0 < k := inv_pos.mpr (Real.sqrt_pos.2 hcpos)
  have hk1 : k ≤ 1 := by dsimp [k]; exact (inv_le_one₀ (Real.sqrt_pos.2 hcpos)).2 hs
  refine ⟨c * C, mul_pos hcpos hC, ?_⟩
  intro z r hr hr1
  let S : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧
        ‖scaledCenteredPlanarPath x c b (Real.toNNReal t) - k • (z - x)‖ < k * r}
  have hS := h (k • (z - x)) (k * r) (mul_pos hk hr) (by nlinarith)
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
  calc
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (C * (k * r) ^ d) := by simpa only [S, mul_comm] using (mul_le_mul_left hS (ENNReal.ofReal c))
    _ ≤ ENNReal.ofReal (c * C * r ^ d) := by
      rw [← ENNReal.ofReal_mul hcpos.le]
      apply ENNReal.ofReal_le_ofReal
      have hp := Real.rpow_le_rpow (mul_nonneg hk.le hr.le) (show k * r ≤ r by nlinarith) hd.le
      nlinarith [mul_nonneg hcpos.le hC.le]

/-- Almost surely, every finite time interval has uniform subcritical ball occupation bounds. -/
theorem planarBrownianMotion_uniform_ball_occupation_all_horizons (x : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ (T d : ℝ), 0 < d → d < 2 →
      ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (r : ℝ), 0 < r → r ≤ 1 →
        volume {t : ℝ | t ∈ Icc (0 : ℝ) T ∧ ‖b (Real.toNNReal t) - z‖ < r} ≤
          ENNReal.ofReal (C * r ^ d) := by
  have hn : ∀ n : ℕ, ∀ᵐ b ∂(planarBrownianMotion x), ∀ d : ℝ, 0 < d → d < 2 →
      ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (r : ℝ), 0 < r → r ≤ 1 →
        volume {t : ℝ | t ∈ Icc (0 : ℝ) (n + 1 : ℕ) ∧
          ‖b (Real.toNNReal t) - z‖ < r} ≤ ENNReal.ofReal (C * r ^ d) := by
    intro n
    let c : ℝ≥0 := n + 1
    have hc : 1 ≤ c := by simp [c]
    have hscale := planarBrownianMotion_map_scaledCenteredPlanarPath x
      (c := c) (ne_of_gt (lt_of_lt_of_le zero_lt_one hc))
    have ha := planarBrownianMotion_uniform_ball_occupation_real_time 0
    rw [← hscale] at ha
    have hb := ae_of_ae_map (continuous_scaledCenteredPlanarPath x c).measurable.aemeasurable ha
    filter_upwards [hb] with b hb d hd0 hd2
    obtain ⟨C, hC, hbound⟩ := hb d hd0 hd2
    simpa [c] using scaled_occupation_bound x b c hc hd0 C hC hbound
  filter_upwards [ae_all_iff.mpr hn] with b hb T d hd0 hd2
  obtain ⟨n, hn⟩ := exists_nat_gt T
  obtain ⟨C, hC, hbound⟩ := hb n d hd0 hd2
  refine ⟨C, hC, ?_⟩
  intro z r hr hr1
  apply le_trans (measure_mono ?_) (hbound z r hr hr1)
  intro t ht
  exact ⟨⟨ht.1.1, ht.1.2.trans (by push_cast; linarith)⟩, ht.2⟩

end HarmonicBalls
