import HarmonicBalls.Proofs.Sec6.ArbitraryRadiusGoodAnnulus
import HarmonicBalls.Proofs.Sec6.EightAdicGoodPrevalence

/-! # Seven-adic good-annulus probability reduction

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`, with the field-law bridge
in `LatticeProb.Bonanno.LQGMetric.Field.GFFLaw`,
`LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate`, and
`LatticeProb.Bonanno.LQGMetric.Field.ExistGFF`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter MarkovProcess
open scoped ENNReal

universe u

/-- A bound at the origin on one whole-plane realization transfers to every
centre and every whole-plane realization at the same positive radius. -/
theorem goodAnnulus_failure_probability_eq_reference
    {γ : ℝ} {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {r a b : ℝ} (hr : 0 < r) (ha : 0 < a) (z : ℂ) :
    P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} =
      P₀ {ω | ¬ IsGoodAnnulus (μ₀ ω) r 0 a b} := by
  have hm := (measurableSet_isGoodAnnulus_of_pos r hr 0 a b ha).compl
  have ht := (identDistrib_translateMeasure h hμ
    (wholePlaneGFFAffineInvariance_proved P hC hcirc) z).measure_mem_eq hm
  change P {ω | ¬ IsGoodAnnulus (μ ω) r 0 a b} =
    P {ω | ¬ IsGoodAnnulus (affineMeasure γ hcirc μ 1 z ω) r 0 a b} at ht
  have ht' : {ω | ¬ IsGoodAnnulus (affineMeasure γ hcirc μ 1 z ω) r 0 a b} =
      {ω | ¬ IsGoodAnnulus (μ ω) r z a b} := by
    ext ω
    simp only [mem_ofPred_eq, isGoodAnnulus_affineMeasure_translate]
  rw [ht'] at ht
  have hd := (h₀.identDistrib_lqgMeasure_across_spaces h hμ₀ hμ).measure_mem_eq hm
  exact ht.symm.trans hd.symm

/-- Seven-adic prevalence follows from a uniform origin-centred probability
bound on one reference realization at the radii `7⁻ⁿ`. This bound is a
proof hypothesis, not a staged literature input. -/
theorem goodAnnuliSubRangeStep_of_sevenAdic_reference_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hprob : ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ b ∈ Ioo (0 : ℝ) 1,
      ∀ p ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω]
        (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc →
        IsLQGMeasureOfField P γ 0 hcirc μ →
        ∃ a ∈ Ioo (0 : ℝ) 1, ∀ n : ℕ,
          P {ω | ¬ IsGoodAnnulus (μ ω) ((7 : ℝ)⁻¹ ^ n) 0 a b} ≤
            ENNReal.ofReal (1 - p)) : GoodAnnuliSubRangeStep.{u} := by
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
    obtain ⟨a, ha, hbound⟩ := hprob γ hγ hγ2 b hb p hp Ω₀ P₀ hC₀ hcirc₀ μ₀ h₀ hμ₀
    refine ⟨a, ha, ?_⟩
    intro Ω _ P hC hcirc μ hgff hμ
    let := hgff.isProbabilityMeasure
    have hAff := wholePlaneGFFAffineInvariance_proved P hC hcirc
    have hrec : ∀ z, IsWholePlaneGFF P (affinePairing hC hcirc 1 z)
        (affineCircle hcirc 1 z) := fun z => hAff hgff 1 one_ne_zero z
    apply hprev Ω P (fun z => affinePairing hC hcirc 1 z)
      (fun z => affineCircle hcirc 1 z) hrec μ a b
    · intro z n
      exact isFieldMeasurableModConst_goodAnnulus_recentered_of_translation
        (lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth) hgff hμ hAff hγ hγ2
        (pow_pos (by norm_num) n) z ha.1 b
        (lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ 0 _ _)
        (by intro v hv x hx hne; exact planarBrownianMotion_point_avoidance v x hne.symm)
    · intro z n
      apply measure_ge_of_compl_le_ofReal P _ hp.1.le hp.2.le
      change P {ω | ¬ IsGoodAnnulus (μ ω) ((7 : ℝ)⁻¹ ^ n) z a b} ≤ _
      rw [goodAnnulus_failure_probability_eq_reference h₀ hμ₀ hgff hμ
        (pow_pos (by norm_num) n) ha.1 z]
      exact hbound n
  · refine ⟨1 / 2, by norm_num, ?_⟩
    intro Ω m P hC hcirc μ hgff hμ
    exact False.elim (hex ⟨Ω, m, P, hC, hcirc, μ, hgff, hμ⟩)

end HarmonicBalls.Section6
