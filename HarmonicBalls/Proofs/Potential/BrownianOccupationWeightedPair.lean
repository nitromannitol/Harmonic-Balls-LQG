import HarmonicBalls.Proofs.Potential.BrownianOccupationNearDiagonal

/-! # Weighted Brownian pair occupation

Bounded spatial weights preserve the near-diagonal pair occupation estimate.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- Almost every Brownian path has a simultaneous near-diagonal pair bound for every
bounded measurable nonnegative spatial weight. -/
theorem planarBrownianMotion_ae_unit_weighted_pair_occupation_le (x : ℂ) {β : ℝ}
    (hβ0 : 0 < β) (hβ2 : β < 2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∃ C : ℝ, 0 < C ∧
      ∀ (g : ℂ → ℝ≥0∞), Measurable g → ∀ M : ℝ≥0∞, M < ∞ →
      (∀ z, g z ≤ M) → ∀ r : ℝ, 0 < r →
        (∫⁻ p : ℝ≥0 × ℝ≥0,
          (if ‖b p.1 - b p.2‖ < r then g (b p.1) * g (b p.2) else 0)
            ∂(ν.prod ν)) ≤ M ^ 2 * ENNReal.ofReal (C * r ^ β) := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  filter_upwards [planarBrownianMotion_ae_unit_pair_occupation_le x hβ0 hβ2] with b hb
  obtain ⟨C, hC, hb⟩ := hb
  refine ⟨C, hC, ?_⟩
  intro g _hg M hM hg r hr
  calc
    (∫⁻ p : ℝ≥0 × ℝ≥0,
        (if ‖b p.1 - b p.2‖ < r then g (b p.1) * g (b p.2) else 0)
          ∂(ν.prod ν)) ≤
        ∫⁻ p : ℝ≥0 × ℝ≥0, M ^ 2 *
          (if ‖b p.1 - b p.2‖ < r then 1 else 0 : ℝ≥0∞) ∂(ν.prod ν) := by
      apply lintegral_mono
      intro p
      dsimp only
      split_ifs with hp
      · simpa [pow_two] using (mul_le_mul' (hg (b p.1)) (hg (b p.2)))
      · simp
    _ = M ^ 2 * (∫⁻ p : ℝ≥0 × ℝ≥0,
        (if ‖b p.1 - b p.2‖ < r then 1 else 0 : ℝ≥0∞) ∂(ν.prod ν)) := by
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top hM.ne)]
    _ ≤ M ^ 2 * ENNReal.ofReal (C * r ^ β) := by gcongr; exact hb r hr

end HarmonicBalls
