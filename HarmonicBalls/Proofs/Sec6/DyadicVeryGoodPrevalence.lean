import HarmonicBalls.Proofs.Sec6.PhaseVeryGoodTranslationLocality
import HarmonicBalls.Proofs.Sec6.DyadicPhaseCriterionProbability
import HarmonicBalls.Proofs.Sec6.VolumeGrowthNonatomic
import HarmonicBalls.Proofs.Sec6.GoodPrevalenceAffine

/-! # Very-good annulus prevalence without coordinate change

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. Translation covariance and
inverse dyadic scaling control the phase of the absolute lattice.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- Every inverse power of eight is an inverse dyadic scale. -/
theorem inverse_eight_pow_eq_dyadicScale (n : ℕ) :
    ((8 : ℝ)⁻¹) ^ n = dyadicScale (3 * n) := by
  unfold dyadicScale
  rw [pow_mul]
  norm_num

/-- A 7-adic good-annulus prevalence estimate yields 8-adic very-good-annulus
grid prevalence under volume growth and affine field invariance. -/
theorem exists_veryGood_prevalence_of_good_prevalence_of_translation
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ξ : Type u} [MeasurableSpace Ξ] (P₀ : Measure Ξ) {γ β a b c : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β) (ha : 0 < a) (hc : 0 < c)
    {hC₀ : Ξ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ξ → ℝ → ℂ → ℝ} {μ₀ : Ξ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    (hAff₀ : WholePlaneGFFAffineInvariance P₀ hC₀ hcirc₀)
    (hprev : PolyHighProb P₀ fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ₀ ω) r z a b}.ncard : ℝ)}) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
        WholePlaneGFFAffineInvariance P hC hcirc →
      PolyHighProb P (fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
        (1 / 64 : ℝ) * Real.logb 8 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (8 : ℝ)⁻¹ ^ n) ∧
            IsVeryGoodAnnulus (μ ω) β r z N a b C₁m C₁p C₂m C₂p c}.ncard : ℝ)}) := by
  obtain ⟨p, hp, hgrid⟩ := veryGoodAnnulus_prevalence_of_fixed_center.{u}
  let δ : ℝ≥0∞ := ENNReal.ofReal ((1 - p) / 3)
  have hδreal : 0 < (1 - p) / 3 := by linarith [hp.2]
  have hδ : 0 < δ := ENNReal.ofReal_pos.2 hδreal
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, hbound⟩ :=
    exists_universal_dyadic_veryGood_probability_of_affine hgrowth P₀ hγ hγ₂ hβ hc
      h₀ hμ₀ hAff₀ hprev ha hδ
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, ?_⟩
  intro N hN Ω _ P hC hcirc μ hgff hμ hAff
  let := hgff.isProbabilityMeasure
  have hrec : ∀ z, IsWholePlaneGFF P (affinePairing hC hcirc 1 z)
      (affineCircle hcirc 1 z) := fun z => hAff hgff 1 one_ne_zero z
  apply hgrid Ω P (fun z => affinePairing hC hcirc 1 z)
    (fun z => affineCircle hcirc 1 z) hrec μ β N a b C₁m C₁p C₂m C₂p c
  · intro z n
    exact isFieldMeasurableModConst_veryGoodAnnulus_recentered_of_translation
      (lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth) hgff hμ hAff hγ hγ₂ z β
      ((8 : ℝ)⁻¹ ^ n) (pow_pos (by norm_num) n) N (hN₀.trans hN)
      a b C₁m C₁p C₂m C₂p c ha
      (lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ 0 _ _)
  · intro z n
    have hsum : δ + δ + δ = ENNReal.ofReal (1 - p) := by
      dsimp [δ]
      rw [← ENNReal.ofReal_add hδreal.le,
        ← ENNReal.ofReal_add (by linarith : 0 ≤ (1 - p) / 3 + (1 - p) / 3)]
      congr 1
      ring
      all_goals exact hδreal.le
    apply measure_ge_of_compl_le_ofReal P _ hp.1.le hp.2.le
    rw [← hsum, inverse_eight_pow_eq_dyadicScale]
    exact hbound N hN Ω P hC hcirc μ hgff hμ hAff (3 * n) z

/-- The whole-plane very-good subrange step follows from the good-annulus
subrange step, volume growth and affine field invariance. -/
theorem veryGoodAnnuliSubRangeStep_of_goodPrevalence_of_translation
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hsub : GoodAnnuliSubRangeStep.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc) : VeryGoodAnnuliSubRangeStep.{u} := by
  obtain ⟨c, hc, hsub⟩ := hsub
  refine ⟨1 / 64, c, by norm_num, hc, ?_⟩
  intro γ hγ hγ₂ β hβ b hb
  obtain ⟨a, ha, hprev⟩ := hsub γ hγ hγ₂ b hb
  by_cases href : ∃ (Ξ : Type u) (mΞ : MeasurableSpace Ξ), letI := mΞ
      ∃ (P₀ : Measure Ξ) (hC₀ : Ξ → (ℂ → ℝ) → ℝ) (hcirc₀ : Ξ → ℝ → ℂ → ℝ)
        (ν₀ : Ξ → Measure ℂ), IsWholePlaneGFF P₀ hC₀ hcirc₀ ∧
          IsLQGMeasureOfField P₀ γ 0 hcirc₀ ν₀
  · obtain ⟨Ξ, mΞ, P₀, hC₀, hcirc₀, ν₀, h₀, hν₀⟩ := href
    let : MeasurableSpace Ξ := mΞ
    obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, hbound⟩ :=
      exists_veryGood_prevalence_of_good_prevalence_of_translation hgrowth P₀ hγ hγ₂
        hβ ha.1 hc h₀ hν₀ (hAff Ξ P₀ hC₀ hcirc₀) (hprev Ξ P₀ hC₀ hcirc₀ ν₀ h₀ hν₀)
    refine ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, by omega, ?_⟩
    intro N hN Ω _ P hC hcirc μ hgff hμ
    exact hbound N hN Ω P hC hcirc μ hgff hμ (hAff Ω P hC hcirc)
  · refine ⟨a, ha, 1, 1, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num,
      9, by omega, ?_⟩
    intro N hN Ω mΩ P hC hcirc μ hgff hμ
    exact False.elim (href ⟨Ω, mΩ, P, hC, hcirc, μ, hgff, hμ⟩)

/-- Lemma 6.6 follows from the good-annulus subrange step, volume growth and
the staged affine and zero-singularity existence hypotheses. -/
theorem manyVeryGoodAnnuliStmt_of_goodPrevalence_of_translation
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hsub : GoodAnnuliSubRangeStep.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc) : ManyVeryGoodAnnuliStmt.{u} := by
  apply manyVeryGoodAnnuliStmt_of_literature
    (veryGoodAnnuliSubRangeStep_of_goodPrevalence_of_translation hgrowth hsub hAff) hex
  intro Ω _ P γ hC hcirc
  exact lqgMeasureWeylScaling Ω P γ 0 hC hcirc

/-- Proposition 6.2 follows from the good-annulus prevalence step, volume
growth and the staged affine and zero-singularity existence hypotheses. -/
theorem harnackTypeComponentStmt_of_goodPrevalence_of_translation
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hsub : GoodAnnuliSubRangeStep.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc) : HarnackTypeComponentStmt.{u} := by
  apply harnackTypeComponentStmt_of_volumeGrowth_and_prevalence hgrowth
    (veryGoodAnnuliSubRangeStep_of_goodPrevalence_of_translation hgrowth hsub hAff) hex
  intro Ω _ P γ hC hcirc
  exact lqgMeasureWeylScaling Ω P γ 0 hC hcirc

/-- Proposition 6.1 follows from the same explicit prevalence and LQG hypotheses. -/
theorem harnackTypeEstimateStmt_of_goodPrevalence_of_translation
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hsub : GoodAnnuliSubRangeStep.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc) : HarnackTypeEstimateStmt.{u} := by
  apply harnackTypeEstimateStmt_of_volumeGrowth_and_prevalence hgrowth
    (veryGoodAnnuliSubRangeStep_of_goodPrevalence_of_translation hgrowth hsub hAff) hex
  intro Ω _ P γ hC hcirc
  exact lqgMeasureWeylScaling Ω P γ 0 hC hcirc

end HarmonicBalls.Section6
