import HarmonicBalls.Proofs.Sec6.PhasePrevalenceAssembly
import HarmonicBalls.Proofs.Sec6.CriterionThreeOffCenterScaling
import HarmonicBalls.Proofs.Sec6.VeryGoodUnionBound
import HarmonicBalls.Proofs.Sec6.SizeRatioTranslationLaw
import HarmonicBalls.Proofs.Sec6.UniversalSizeWindows

/-! # Uniform very-good-annulus probability and grid prevalence

The imported annulus iteration uses Leonardo Bonanno's proof of the
Gwynne–Miller lemma in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- Whole-plane good-annulus prevalence and volume growth give a uniform
one-scale lower bound for the very-good event at every center and radius. -/
theorem exists_wholePlane_veryGoodAnnulus_probability_uniform
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {γ β : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {a b c : ℝ} (hc : 0 < c)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hprev : PolyHighProb P fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ (ρ : ℝ), 0 < ρ → ∀ z : ℂ,
        ENNReal.ofReal p ≤ P {ω | IsVeryGoodAnnulus (μ ω) β ρ z N
          a b C₁m C₁p C₂m C₂p c} := by
  let := hgff.isProbabilityMeasure
  let δ : ℝ≥0∞ := ENNReal.ofReal ((1 - p) / 3)
  have hδreal : 0 < (1 - p) / 3 := by linarith [hp.2]
  have hδ : 0 < δ := ENNReal.ofReal_pos.2 hδreal
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, hsize⟩ :=
    exists_wholePlane_veryGood_size_windows_uniform hgrowth P hγ hγ₂ hβ
      hgff hμ hAff hCC hδ
  obtain ⟨N₀, hN₀, hthree⟩ := exists_universal_criterionThree_probability
    P hγ hγ₂ hc hgff hμ hAff hCC hprev hunit hδ
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, ?_⟩
  intro N hN ρ hρ z
  have hfail : P {ω | ¬ IsVeryGoodAnnulus (μ ω) β ρ z N
      a b C₁m C₁p C₂m C₂p c} ≤ δ + δ + δ := by
    calc
      _ ≤ _ := measure_not_veryGoodAnnulus_le P μ β ρ z N a b C₁m C₁p C₂m C₂p c
      _ ≤ δ + δ + δ := add_le_add (add_le_add (hsize ρ hρ z).1
        (hsize ρ hρ z).2) (hthree N hN Ω P hC hcirc μ hgff hμ hAff hCC ρ hρ z)
  have hsum : δ + δ + δ = ENNReal.ofReal (1 - p) := by
    dsimp [δ]
    rw [← ENNReal.ofReal_add hδreal.le,
      ← ENNReal.ofReal_add (by linarith : 0 ≤ (1 - p) / 3 + (1 - p) / 3)]
    congr 1
    ring
    all_goals exact hδreal.le
  apply measure_ge_of_compl_le_ofReal P _ hp.1.le hp.2.le
  simpa only [Set.compl_ofPred, hsum] using hfail

/-- Whole-plane good-annulus prevalence and volume growth give a uniform
one-scale lower bound for the very-good event at every center and radius. -/
theorem exists_universal_wholePlane_veryGoodAnnulus_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {γ β : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {a b c : ℝ} (hc : 0 < c)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hprev : PolyHighProb P fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω')
        (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ' : Ω' → Measure ℂ),
        IsWholePlaneGFF P' hC' hcirc' → IsLQGMeasureOfField P' γ 0 hcirc' μ' →
        WholePlaneGFFAffineInvariance P' hC' hcirc' → LQGMeasureCoordChange P' γ 0 hC' hcirc' →
      ∀ (ρ : ℝ), 0 < ρ → ∀ z : ℂ,
        ENNReal.ofReal p ≤ P' {ω | IsVeryGoodAnnulus (μ' ω) β ρ z N
          a b C₁m C₁p C₂m C₂p c} := by
  let δ : ℝ≥0∞ := ENNReal.ofReal ((1 - p) / 3)
  have hδreal : 0 < (1 - p) / 3 := by linarith [hp.2]
  have hδ : 0 < δ := ENNReal.ofReal_pos.2 hδreal
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, hsize⟩ :=
    exists_universal_wholePlane_size_windows hgrowth hγ hγ₂ hβ P hgff hμ hδ
  obtain ⟨N₀, hN₀, hthree⟩ := exists_universal_criterionThree_probability
    P hγ hγ₂ hc hgff hμ hAff hCC hprev hunit hδ
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, ?_⟩
  intro N hN Ω' _ P' hC' hcirc' μ' hgff' hμ' hAff' hCC' ρ hρ z
  let := hgff'.isProbabilityMeasure
  have hs := hsize Ω' P' hC' hcirc' μ' hgff' hμ' hAff' hCC' ρ hρ z
  have hfail : P' {ω | ¬ IsVeryGoodAnnulus (μ' ω) β ρ z N
      a b C₁m C₁p C₂m C₂p c} ≤ δ + δ + δ := by
    calc
      _ ≤ _ := measure_not_veryGoodAnnulus_le P' μ' β ρ z N a b C₁m C₁p C₂m C₂p c
      _ ≤ δ + δ + δ := add_le_add (add_le_add hs.1 hs.2) (hthree N hN Ω' P' hC' hcirc' μ' hgff' hμ' hAff' hCC' ρ hρ z)
  have hsum : δ + δ + δ = ENNReal.ofReal (1 - p) := by
    dsimp [δ]
    rw [← ENNReal.ofReal_add hδreal.le,
      ← ENNReal.ofReal_add (by linarith : 0 ≤ (1 - p) / 3 + (1 - p) / 3)]
    congr 1
    ring
    all_goals exact hδreal.le
  apply measure_ge_of_compl_le_ofReal P' _ hp.1.le hp.2.le
  simpa only [Set.compl_ofPred, hsum] using hfail

/-- Whole-plane good-annulus prevalence implies very-good-annulus grid
prevalence, under the explicit affine and LQG regularity hypotheses. -/
theorem exists_wholePlane_veryGoodAnnulus_grid_prevalence
    (hfull : LQGMeasureFullSupportStmt.{u}) (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {γ β : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {a b c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hatom : ∀ z : ℂ, LQGMeasureNonatomic P γ 0 (affinePairing hC hcirc 1 z)
      (affineCircle hcirc 1 z))
    (hprev : PolyHighProb P fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      PolyHighProb P (fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
        (1 / 64 : ℝ) * Real.logb 8 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (8 : ℝ)⁻¹ ^ n) ∧
            IsVeryGoodAnnulus (μ ω) β r z N a b C₁m C₁p C₂m C₂p c}.ncard : ℝ)}) := by
  obtain ⟨p, hp, hgrid⟩ := veryGoodAnnulus_prevalence_of_affine_fixed_center_bounds hfull
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, hbound⟩ :=
    exists_wholePlane_veryGoodAnnulus_probability_uniform hgrowth P hγ hγ₂ hβ hc
      hgff hμ hAff hCC hprev hunit hp
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, ?_⟩
  intro N hN
  apply hgrid Ω P γ hC hcirc hgff μ hμ hAff hCC hγ hγ₂ hatom β N (hN₀.trans hN)
    a b C₁m C₁p C₂m C₂p c ha
  intro z n
  exact hbound N hN _ (pow_pos (by norm_num) n) z

/-- Whole-plane very-good-annulus prevalence follows from good-annulus
prevalence and the explicit LQG regularity and affine-law hypotheses. -/
theorem veryGoodAnnuliSubRangeStep_of_goodAnnuliSubRangeStep
    (hfull : LQGMeasureFullSupportStmt.{u}) (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hsub : GoodAnnuliSubRangeStep.{u})
    (hatom : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ 0 hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc) : VeryGoodAnnuliSubRangeStep.{u} := by
  classical
  obtain ⟨c, hc, hsub⟩ := hsub
  refine ⟨1 / 64, c, by norm_num, hc, ?_⟩
  intro γ hγ hγ₂ β hβ b hb
  obtain ⟨a, ha, hprev⟩ := hsub γ hγ hγ₂ b hb
  have hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b} := by
    apply measurableSet_isGoodAnnulus_of_ae_point_avoidance 1 (by norm_num) 0 a b ha.1
    intro v _ x _ hxv
    exact planarBrownianMotion_point_avoidance v x hxv.symm
  obtain ⟨p, hp, hgrid⟩ := veryGoodAnnulus_prevalence_of_affine_fixed_center_bounds hfull
  by_cases href : ∃ (Ω₀ : Type u) (m₀ : MeasurableSpace Ω₀),
      letI := m₀
      ∃ (P₀ : Measure Ω₀) (hC₀ : Ω₀ → (ℂ → ℝ) → ℝ)
        (hcirc₀ : Ω₀ → ℝ → ℂ → ℝ) (μ₀ : Ω₀ → Measure ℂ),
        IsWholePlaneGFF P₀ hC₀ hcirc₀ ∧ IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀
  · obtain ⟨Ω₀, m₀, P₀, hC₀, hcirc₀, μ₀, hgff₀, hμ₀⟩ := href
    let : MeasurableSpace Ω₀ := m₀
    obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₁, hN₁, hprob⟩ :=
      exists_universal_wholePlane_veryGoodAnnulus_probability hgrowth P₀ hγ hγ₂ hβ hc
        hgff₀ hμ₀ (hAff Ω₀ P₀ hC₀ hcirc₀) (hCC Ω₀ P₀ γ hC₀ hcirc₀)
        (hprev Ω₀ P₀ hC₀ hcirc₀ μ₀ hgff₀ hμ₀) hunit hp
    refine ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₁, by omega, ?_⟩
    intro N hN Ω _ P hC hcirc μ hgff hμ
    apply hgrid Ω P γ hC hcirc hgff μ hμ (hAff Ω P hC hcirc)
      (hCC Ω P γ hC hcirc) hγ hγ₂
      (fun z => hatom Ω P γ (affinePairing hC hcirc 1 z) (affineCircle hcirc 1 z))
      β N (hN₁.trans hN) a b C₁m C₁p C₂m C₂p c ha.1
    intro z n
    exact hprob N hN Ω P hC hcirc μ hgff hμ (hAff Ω P hC hcirc)
      (hCC Ω P γ hC hcirc) _ (pow_pos (by norm_num) n) z
  · refine ⟨a, ha, 1, 1, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num,
      9, by omega, ?_⟩
    intro N hN Ω mΩ P hC hcirc μ hgff hμ
    exfalso
    exact href ⟨Ω, mΩ, P, hC, hcirc, μ, hgff, hμ⟩

end HarmonicBalls.Section6
