import HarmonicBalls.Proofs.Sec6.SingularWeight
import HarmonicBalls.Proofs.Sec2.SingularWeight

/-!
# Removing the logarithmic singularity in Lemma 6.4

The zero-singularity probability estimate, LQG measure existence, and Weyl scaling imply the
full good-annulus probability estimate. The threshold loss retains its dependence on `α₀`.
The staged literature hypotheses remain subject to operator source-check.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- Reduce Lemma 6.4 to its zero-singularity case using measure existence and Weyl scaling. -/
theorem goodAnnulusProbabilityStmt_of_zero
    (hzero : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ b ∈ Ioo (0 : ℝ) 1, ∀ p ∈ Ioo (0 : ℝ) 1, ∃ a ∈ Ioo (0 : ℝ) 1,
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      ∀ r : ℝ, 0 < r → ∀ z : ℂ, r / 100 ≤ infDist (0 : ℂ) (annulus z (3 * r) (5 * r)) →
        P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} ≤ ENNReal.ofReal (1 - p))
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureWeylScaling P γ 0 hC hcirc) : GoodAnnulusProbabilityStmt.{u} := by
  intro γ α₀ hγ hγ2 hα₀ b hb p hp
  obtain ⟨a, ha, hgood⟩ := hzero γ hγ hγ2 b hb p hp
  let t : ℝ := (1001 : ℝ) ^ |-(γ * α₀)|
  have ht : 1 ≤ t := Real.one_le_rpow (by norm_num) (abs_nonneg _)
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  refine ⟨a / t ^ 2, ⟨div_pos ha.1 (sq_pos_of_pos htpos), ?_⟩, ?_⟩
  · rw [div_lt_one (sq_pos_of_pos htpos)]
    nlinarith [ha.2]
  intro Ω _ P hC hcirc μ hGFF hμ r hr z hd
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := hex Ω P γ hC hcirc hGFF hγ hγ2 hQ
  have hweight := singularWeightStep_of_weyl hW γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ μ₀ hGFF hμ hμ₀
  exact (Section6.badGoodAnnulus_measure_le_of_singular_weight P hr hd hweight).trans
    (hgood Ω P hC hcirc μ₀ hGFF hμ₀ r hr z hd)

end HarmonicBalls
