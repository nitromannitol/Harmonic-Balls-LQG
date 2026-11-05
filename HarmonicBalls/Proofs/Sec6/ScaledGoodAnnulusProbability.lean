import HarmonicBalls.Proofs.Sec6.ScaledGoodAnnulusIteration
import HarmonicBalls.Proofs.Sec6.GoodAnnulusUniformProbability

/-! # Scaled seven-adic good-annulus counts

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- A polynomial lower-tail estimate for the normalized seven-adic count,
uniform over every positive physical scale and deterministic centre. -/
theorem exists_scaled_goodAnnulus_count_tail_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {b : ℝ} (hb : 0 < b) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
    ∀ (s : ℝ), 0 < s → ∀ (z : ℂ) (ε : ℝ), 0 < ε →
      16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      P {ω | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧ IsGoodAnnulus (μ ω) (s * r) z a b}.ncard : ℝ) <
          (1 / 32 : ℝ) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤ ENNReal.ofReal (C * ε ^ (6 : ℝ)) := by
  have hlog : 0 < Real.log 7 := Real.log_pos (by norm_num)
  obtain ⟨p, hp, C, hC, hiter⟩ := scaled_goodAnnulus_subrange_probability
    (96 * Real.log 7) (1 / 2) (by positivity) (by norm_num)
  obtain ⟨a, ha, hprob⟩ := exists_universal_goodAnnulus_probability_all_radii
    hgrowth hγ hγ₂ h₀ hμ₀ hb hp
  refine ⟨a, ha, C, hC, ?_⟩
  intro Ω _ P hCfield hcirc μ hgff hμ s hs z ε hε ht
  let := hgff.isProbabilityMeasure
  have hAff := wholePlaneGFFAffineInvariance_proved P hCfield hcirc
  have hrec := hAff hgff 1 one_ne_zero z
  have htail := hiter Ω P (affinePairing hCfield hcirc 1 z) (affineCircle hcirc 1 z)
    hrec μ z a b s hs
    (by
      intro n
      exact isFieldMeasurableModConst_goodAnnulus_recentered_of_translation
        (lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth) hgff hμ hAff hγ hγ₂
        (mul_pos hs (pow_pos (by norm_num) n)) z ha.1 b
        (lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ 0 _ _)
        (by intro v hv x hx hne; exact planarBrownianMotion_point_avoidance v x hne.symm))
    (by
      intro n
      apply measure_ge_of_compl_le_ofReal P _ hp.1.le hp.2.le
      exact hprob Ω P hCfield hcirc μ hgff hμ _ (mul_pos hs (pow_pos (by norm_num) n)) z)
    ε hε ht
  have hexp : 96 * Real.log 7 / (16 * Real.log 7) = (6 : ℝ) := by field_simp; norm_num
  simpa only [hexp, show (1 / 2 : ℝ) / 16 = 1 / 32 by norm_num] using htail

end HarmonicBalls.Section6
