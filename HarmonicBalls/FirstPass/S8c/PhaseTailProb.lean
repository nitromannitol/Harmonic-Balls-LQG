import HarmonicBalls.Proofs.Sec8.UniformPhasePrevalenceAssembly
import HarmonicBalls.FirstPass.S8c.PhaseTail

/-! # The probability part (9) of the phase tail (G-8-2 section 3)

`exists_uniform_singular_phase_probability_of_subrange` (Proofs/Sec8/UniformPhasePrevalenceAssembly.lean) is the
per-phase, uniform-in-`Ω` bound of G-8-2 eq. (9) for the insertion-`γ` measure `ν`: at unit outer scale, for every
constant lattice phase `q`, the failure probability of the phase-sensitive very-good event (with the constants
`a/((401^{γ²})²)`, `b`, `c = C₃`) and of the annulus-ball comparison is at most `δ + δ + δ + δ`. This file
specializes it to `α = γ` and to `δ = ζ/8`, giving failure probability at most `ζ`, with the constant structure of
`LocalPhaseTailStep` (PhaseTail.lean). The inputs are those of the existing theorem and are passed through
as hypotheses: the Draft statements `LQGVolumeGrowthAllScalesStmt` and `LQGMeasureFullSupportStmt`, the Step
`GoodAnnuliSubRangeStep`, and the Proposed universal existence, Weyl, affine and coordinate-change inputs.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- The per-phase probability bound (9) of the phase tail, for the insertion-`γ` measure, at failure level `ζ`. -/
theorem localPhaseTail_failure_le (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hfull : LQGMeasureFullSupportStmt.{u}) (hsub : GoodAnnuliSubRangeStep.{u})
    (hEx : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α hC hcirc) :
    ∃ c : ℝ, 0 < c ∧ ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ β : ℝ, (2 + γ) ^ 2 / 2 < β →
    ∀ ζ : ℝ, 0 < ζ → ∀ b ∈ Ioo (0 : ℝ) 1,
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∃ m ∈ Ioo (0 : ℝ) 1, ∀ N : ℕ, N₀ ≤ N →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ →
        ∀ q : ℂ, P {ω | ¬ (PhaseVeryGoodAnnulus (μ ω) β 1 0 N
          (a / (((401 : ℝ) ^ |-(γ * γ)|) ^ 2)) b C₁m C₁p C₂m C₂p c q ∧
          AnnulusBallComparison (μ ω) 0 0 m)} ≤ ENNReal.ofReal (ζ / 2) := by
  obtain ⟨c, hc, h⟩ := exists_uniform_singular_phase_probability_of_subrange hgrowth hfull hsub
  refine ⟨c, hc, fun γ hγ0 hγ2 β hβ ζ hζ b hb => ?_⟩
  have hγQ : γ < lqgQ γ := by
    unfold lqgQ
    have hprod : 0 < (2 - γ) * (2 + γ) := mul_pos (by linarith) (by linarith)
    have hdiv : γ / 2 < 2 / γ := (div_lt_div_iff₀ (by norm_num) hγ0).2 (by nlinarith)
    linarith
  obtain ⟨a, ha, hδ⟩ := h γ γ β hγ0 hγ2 hγQ hβ b hb
  refine ⟨a, ha, ?_⟩
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h1, h2, h3, h4, N₀, hN₀, m, hm, hall⟩ :=
    hδ (ENNReal.ofReal (ζ / 8)) (ENNReal.ofReal_pos.mpr (by linarith))
  refine ⟨C₁m, C₁p, C₂m, C₂p, h1, h2, h3, h4, N₀, hN₀, m, hm, fun N hN Ω _ P hC hcirc μ hGFF hμ q => ?_⟩
  have hbound := hall N hN Ω P hC hcirc μ hGFF hμ (hEx Ω P γ 0 hC hcirc) (hW Ω P γ hC hcirc)
    (hAff Ω P hC hcirc) (hCC Ω P γ 0 hC hcirc) (hCC Ω P γ γ hC hcirc) q
  have hsum : ENNReal.ofReal (ζ / 8) + ENNReal.ofReal (ζ / 8) + ENNReal.ofReal (ζ / 8) +
      ENNReal.ofReal (ζ / 8) = ENNReal.ofReal (ζ / 2) := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith),
      ← ENNReal.ofReal_add (by linarith) (by linarith),
      ← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1
    ring
  exact hbound.trans hsum.le


end HarmonicBalls
