import HarmonicBalls.Proofs.Sec6.PhaseVeryGoodFieldLocality
import HarmonicBalls.Proofs.Sec6.PrevalenceGridUnion

/-! # Very-good-annulus grid prevalence from affine locality

The imported annulus iteration uses Leonardo Bonanno's proof of the
Gwynne–Miller lemma in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- Fixed-center probability bounds imply grid prevalence once affine locality
and the explicit LQG regularity hypotheses are available. -/
theorem veryGoodAnnulus_prevalence_of_affine_fixed_center_bounds
    (hfull : LQGMeasureFullSupportStmt.{u}) :
    ∃ p ∈ Ioo (0 : ℝ) 1,
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (_hgff : IsWholePlaneGFF P hC hcirc) (μ : Ω → Measure ℂ)
      (_hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
      (_hAff : WholePlaneGFFAffineInvariance P hC hcirc)
      (_hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
      (_hγ : 0 < γ) (_hγ2 : γ < 2)
      (_hatom : ∀ z : ℂ, LQGMeasureNonatomic P γ 0 (affinePairing hC hcirc 1 z)
        (affineCircle hcirc 1 z))
      (βminus : ℝ) (N : ℕ) (_hN : 9 ≤ N)
      (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (_ha : 0 < a),
      (∀ z : ℂ, ∀ n : ℕ, ENNReal.ofReal p ≤ P {ω |
        IsVeryGoodAnnulus (μ ω) βminus ((8 : ℝ)⁻¹ ^ n) z N
          a b C₁m C₁p C₂m C₂p C₃}) →
      PolyHighProb P (fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
        (1 / 64 : ℝ) * Real.logb 8 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (8 : ℝ)⁻¹ ^ n) ∧
            IsVeryGoodAnnulus (μ ω) βminus r z N a b C₁m C₁p C₂m C₂p C₃}.ncard : ℝ)}) := by
  obtain ⟨p, hp, hprev⟩ := veryGoodAnnulus_prevalence_of_fixed_center
  refine ⟨p, hp, ?_⟩
  intro Ω _ P γ hC hcirc hgff μ hμ hAff hCC hγ hγ2 hatom βminus N hN
    a b C₁m C₁p C₂m C₂p C₃ ha hprob
  apply hprev Ω P (fun z => affinePairing hC hcirc 1 z)
    (fun z => affineCircle hcirc 1 z) (fun z => hAff hgff 1 one_ne_zero z)
    μ βminus N a b C₁m C₁p C₂m C₂p C₃ ?_ hprob
  intro z n
  exact isFieldMeasurableModConst_veryGoodAnnulus_recentered hfull hgff hμ hAff hCC
    hγ hγ2 z βminus ((8 : ℝ)⁻¹ ^ n) (pow_pos (by norm_num) n) N hN
    a b C₁m C₁p C₂m C₂p C₃ ha (hatom z)

end HarmonicBalls.Section6
