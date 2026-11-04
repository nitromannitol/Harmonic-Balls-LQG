import HarmonicBalls.Proofs.Sec6.PrevalenceGridUnion
import HarmonicBalls.Proofs.Sec6.GoodAnnulusAffineLaw
import HarmonicBalls.Proofs.Sec6.GoodAnnulusRegularLaw
import HarmonicBalls.Steps.Sec6.Prevalence

/-! # Whole-plane good-annulus prevalence

The annulus iteration uses Leonardo Bonanno's proof of Gwynne–Miller's lemma,
via `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`,
`LatticeProb.Bonanno.LQGMetric.Field.GFFLaw`,
`LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate`, and
`LatticeProb.Bonanno.LQGMetric.Field.ExistGFF`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal

/-- A bound on the outer measure of a failure event yields the corresponding
lower bound on the outer measure of the event, without measurability. -/
theorem measure_ge_of_compl_le_ofReal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : Set Ω) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (h : P Eᶜ ≤ ENNReal.ofReal (1 - p)) : ENNReal.ofReal p ≤ P E := by
  have hsum : (1 : ℝ≥0∞) ≤ P E + P Eᶜ := by
    simpa only [Set.union_compl_self, measure_univ] using (measure_union_le E Eᶜ :
      P (E ∪ Eᶜ) ≤ P E + P Eᶜ)
  have hsum' : (1 : ℝ≥0∞) ≤ P E + ENNReal.ofReal (1 - p) :=
    hsum.trans (by gcongr)
  have hid : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
    rw [← ENNReal.ofReal_add hp0 (by linarith : 0 ≤ 1 - p)]
    simp
  rw [← hid] at hsum'
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hsum'

/-- Under the staged affine laws, a unit-annulus threshold yields prevalence
once each good-annulus event has its recentered mod-constant locality witness. -/
theorem exists_goodAnnulus_prevalence_of_ae_unit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    {b : ℝ} (hmeas : ∀ n : ℕ, MeasurableSet
      {ν : Measure ℂ | IsGoodAnnulus ν 1 0 ((1 / 2 : ℝ) ^ (n + 1)) b})
    (hae : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (μ ω) 1 0 a b)
    (hlocal : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ z : ℂ, ∀ n : ℕ,
      IsFieldMeasurableModConst P 0 (affinePairing hC hcirc 1 z)
        (annulus 0 (3 * ((7 : ℝ)⁻¹ ^ n)) (5 * ((7 : ℝ)⁻¹ ^ n)))
        {ω | IsGoodAnnulus (μ ω) ((7 : ℝ)⁻¹ ^ n) z a b}) :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      PolyHighProb P (fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
        (1 / 32 : ℝ) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)}) := by
  let := hgff.isProbabilityMeasure
  obtain ⟨p, hp, hprev⟩ := goodAnnulus_prevalence_of_fixed_center
  obtain ⟨a, ha, hprob⟩ := exists_uniform_goodAnnulus_probability_of_ae_unit
    hγ hγ2 hgff hμ hAff hCC b hmeas hae hp
  refine ⟨a, ha, ?_⟩
  have hrec : ∀ z, IsWholePlaneGFF P (affinePairing hC hcirc 1 z)
      (affineCircle hcirc 1 z) := by
    intro z
    exact hAff hgff 1 (by norm_num) z
  apply hprev Ω P (fun z => affinePairing hC hcirc 1 z)
    (fun z => affineCircle hcirc 1 z) hrec μ a b (hlocal a ha)
  intro z n
  apply measure_ge_of_compl_le_ofReal P _ hp.1.le hp.2.le
  exact hprob _ (pow_pos (by norm_num) n) z

universe u

open MarkovProcess in
/-- The whole-plane good-annulus prevalence step follows from recentered
annular locality and the unit-threshold and LQG hypotheses used to establish
its one-radius probability bound. -/
theorem goodAnnuliSubRangeStep_of_ae_unit_and_locality
    (hfull : LQGMeasureFullSupportStmt.{u})
    (hatom : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ 0 hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hpolar : ∀ v ∈ sphere (0 : ℂ) (4 * 1),
      ∀ x ∈ annulus 0 (3 * 1) (5 * 1), x ≠ v →
      ∀ᵐ path ∂(planarBrownianMotion v), ∀ t : ℝ≥0, path t ≠ x)
    (hunit : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type u) [MeasurableSpace Ω]
      (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc →
      IsLQGMeasureOfField P γ 0 hcirc μ → ∀ b ∈ Ioo (0 : ℝ) 1,
      ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (μ ω) 1 0 a b)
    (hlocal : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type u) [MeasurableSpace Ω]
      (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc →
      IsLQGMeasureOfField P γ 0 hcirc μ → ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      ∀ z : ℂ, ∀ n : ℕ, IsFieldMeasurableModConst P 0 (affinePairing hC hcirc 1 z)
        (annulus 0 (3 * ((7 : ℝ)⁻¹ ^ n)) (5 * ((7 : ℝ)⁻¹ ^ n)))
        {ω | IsGoodAnnulus (μ ω) ((7 : ℝ)⁻¹ ^ n) z a b}) :
    GoodAnnuliSubRangeStep.{u} := by
  classical
  refine ⟨1 / 32, by norm_num, ?_⟩
  intro γ hγ hγ2 b hb
  obtain ⟨p, hp, hprev⟩ := goodAnnulus_prevalence_of_fixed_center.{u}
  by_cases hex : ∃ (Ω : Type u) (m : MeasurableSpace Ω), letI := m
      ∃ (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc ∧
          IsLQGMeasureOfField P γ 0 hcirc μ
  · obtain ⟨Ω₀, m₀, P₀, hC₀, hcirc₀, μ₀, h₀, hμ₀⟩ := hex
    let : MeasurableSpace Ω₀ := m₀
    obtain ⟨a, ha, hprob⟩ :=
      exists_universal_goodAnnulus_probability_of_ae_unit_of_point_avoidance
        hfull hγ hγ2 (fun Ω _ P hC hcirc => hatom Ω P γ hC hcirc)
        h₀ hμ₀ b hpolar (hunit γ hγ hγ2 Ω₀ P₀ hC₀ hcirc₀ μ₀ h₀ hμ₀ b hb) hp
    refine ⟨a, ha, ?_⟩
    intro Ω _ P hC hcirc μ hgff hμ
    let := hgff.isProbabilityMeasure
    have hrec : ∀ z, IsWholePlaneGFF P (affinePairing hC hcirc 1 z)
        (affineCircle hcirc 1 z) := by
      intro z
      exact hAff Ω P hC hcirc hgff 1 (by norm_num) z
    apply hprev Ω P (fun z => affinePairing hC hcirc 1 z)
      (fun z => affineCircle hcirc 1 z) hrec μ a b
      (hlocal γ hγ hγ2 Ω P hC hcirc μ hgff hμ a ha b hb)
    intro z n
    apply measure_ge_of_compl_le_ofReal P _ hp.1.le hp.2.le
    exact hprob Ω P hC hcirc μ hgff hμ (hAff Ω P hC hcirc)
      (hCC Ω P γ hC hcirc) _ (pow_pos (by norm_num) n) z
  · refine ⟨1 / 2, by norm_num, ?_⟩
    intro Ω m P hC hcirc μ hgff hμ
    exact False.elim (hex ⟨Ω, m, P, hC, hcirc, μ, hgff, hμ⟩)

end HarmonicBalls.Section6
