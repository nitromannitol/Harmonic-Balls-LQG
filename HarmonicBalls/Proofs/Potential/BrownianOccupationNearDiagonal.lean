import HarmonicBalls.Proofs.Potential.BrownianOccupationRieszEnergy

/-! # Brownian near-diagonal occupation

Finite occupation energy bounds the number of close pairs of times.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- Almost every Brownian path has a simultaneous near-diagonal pair bound. -/
theorem planarBrownianMotion_ae_unit_pair_occupation_le (x : ℂ) {β : ℝ}
    (hβ0 : 0 < β) (hβ2 : β < 2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      (∫⁻ p : ℝ≥0 × ℝ≥0,
        (if ‖b p.1 - b p.2‖ < r then 1 else 0 : ℝ≥0∞) ∂(ν.prod ν)) ≤
          ENNReal.ofReal (C * r ^ β) := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  filter_upwards [planarBrownianMotion_ae_unit_occupation_riesz_energy_lt_top x hβ0 hβ2] with b hb
  let E := ∫⁻ p : ℝ≥0 × ℝ≥0, (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-β) ∂(ν.prod ν)
  have hE : E < ∞ := hb
  refine ⟨E.toReal + 1, by positivity, ?_⟩
  intro r hr
  have hrpow : 0 < r ^ β := Real.rpow_pos_of_pos hr _
  have hR0 : ENNReal.ofReal (r ^ β) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hrpow)
  have hRtop : ENNReal.ofReal (r ^ β) ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    (∫⁻ p : ℝ≥0 × ℝ≥0,
        (if ‖b p.1 - b p.2‖ < r then 1 else 0 : ℝ≥0∞) ∂(ν.prod ν)) ≤
        ∫⁻ p : ℝ≥0 × ℝ≥0, ENNReal.ofReal (r ^ β) *
          (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-β) ∂(ν.prod ν) := by
      apply lintegral_mono
      intro p
      dsimp only
      split_ifs with hp
      · have hpow : (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ β ≤ ENNReal.ofReal (r ^ β) := by
          rw [← ENNReal.ofReal_rpow_of_nonneg (le_of_lt hr) (le_of_lt hβ0)]
          exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (le_of_lt hp)) (le_of_lt hβ0)
        rw [ENNReal.rpow_neg]
        calc
          1 = ENNReal.ofReal (r ^ β) * (ENNReal.ofReal (r ^ β))⁻¹ :=
            (ENNReal.mul_inv_cancel hR0 hRtop).symm
          _ ≤ ENNReal.ofReal (r ^ β) * ((ENNReal.ofReal ‖b p.1 - b p.2‖) ^ β)⁻¹ :=
            by gcongr
      · exact bot_le
    _ = ENNReal.ofReal (r ^ β) * E := by rw [lintegral_const_mul' _ _ hRtop]
    _ ≤ ENNReal.ofReal ((E.toReal + 1) * r ^ β) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      have hE' : E ≤ ENNReal.ofReal (E.toReal + 1) := by
        rw [ENNReal.ofReal_add (ENNReal.toReal_nonneg) (by norm_num)]
        rw [ENNReal.ofReal_toReal hE.ne]
        simp
      calc
        ENNReal.ofReal (r ^ β) * E ≤ ENNReal.ofReal (r ^ β) * ENNReal.ofReal (E.toReal + 1) := by gcongr
        _ = ENNReal.ofReal (E.toReal + 1) * ENNReal.ofReal (r ^ β) := mul_comm _ _

end HarmonicBalls
