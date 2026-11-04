import HarmonicBalls.Proofs.Sec6.DyadicVeryGoodPrevalence
import HarmonicBalls.Proofs.Sec6.GoodAnnulusDyadicLaw
import HarmonicBalls.Proofs.Sec6.RecenteredLocalityTranslation
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly

/-! # Eight-adic good-annulus prevalence

The annulus iteration uses Leonardo Bonanno's proof of the Gwynne–Miller
lemma in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`, with the GFF law
bridge in `LatticeProb.Bonanno.LQGMetric.Field.GFFLaw`,
`LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate`, and
`LatticeProb.Bonanno.LQGMetric.Field.ExistGFF`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter MarkovProcess
open scoped ENNReal

universe u

/-- A universal good-annulus threshold gives prevalence at inverse powers of
8, uniformly over whole-plane realizations. -/
theorem exists_eightAdic_goodAnnulus_prevalence
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ}
    {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {b : ℝ} (hb : 0 < b) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      PolyHighProb P (fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
        (1 / 32 : ℝ) * Real.logb 8 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (8 : ℝ)⁻¹ ^ n) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)}) := by
  classical
  have hlog : 0 < Real.log 8 := Real.log_pos (by norm_num)
  obtain ⟨p, hp, C, hCpos, hiter⟩ :=
    annulus_iteration_geometric_count (3 / 8) (5 / 8) (96 * Real.log 8) (1 / 2)
      ((8 : ℝ)⁻¹) 8 1 (by norm_num) (by norm_num) (by norm_num)
      (by positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by omega) (by norm_num)
  obtain ⟨a, ha, hprob⟩ := exists_universal_goodAnnulus_probability_dyadic
    hgrowth hγ hγ2 h₀ hμ₀ (wholePlaneGFFAffineInvariance_proved P₀ hC₀ hcirc₀) hb hp
  refine ⟨a, ha, ?_⟩
  intro Ω _ P hC hcirc μ hgff hμ
  let := hgff.isProbabilityMeasure
  have hAff := wholePlaneGFFAffineInvariance_proved P hC hcirc
  obtain ⟨r₀, hr₀, hr⟩ := exists_radius_logb_inverse_ge (b := 8) (D := 16) (by norm_num)
  apply polyHighProb_forall_prevalenceGrid_of_fixed_center P _ (q := 6) (C := C)
    (by norm_num) hr₀
  intro ε hε hεr z hz
  have ht := hr ε hε hεr
  obtain ⟨n₀, K, hK, hrange⟩ :=
    exists_inverse_geometric_scales_in_three_quarter_window (b := (8 : ℝ))
      (by norm_num) hε 1 (by omega) (by simpa using ht)
  have hK' : Real.logb 8 (ε ^ (-1 : ℝ)) / 16 ≤ (K : ℝ) := by simpa using hK
  have hrec := hAff hgff 1 one_ne_zero z
  have hcount := hiter 0 Ω P (affinePairing hC hcirc 1 z) (affineCircle hcirc 1 z)
    hrec n₀ ε (ε ^ (3 / 4 : ℝ)) hε (fun ω r => IsGoodAnnulus (μ ω) r z a b)
    (by
      intro k
      have hloc := isFieldMeasurableModConst_goodAnnulus_recentered_of_translation
        (lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth) hgff hμ hAff hγ hγ2
        (pow_pos (by norm_num : (0 : ℝ) < 8⁻¹) (n₀ + 1 * k)) z ha.1 b
        (lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ 0 _ _)
        (by intro v hv x hx hne; exact planarBrownianMotion_point_avoidance v x hne.symm)
      convert hloc using 1; norm_num [mul_assoc]
      congr 1 <;> ring)
    (by
      intro k
      apply measure_ge_of_compl_le_ofReal P _ hp.1.le hp.2.le
      rw [inverse_eight_pow_eq_dyadicScale]
      exact hprob Ω P hC hcirc μ hgff hμ hAff _ z)
    K (by simpa using hrange)
  have hthreshold : (1 / 32 : ℝ) * Real.logb 8 (ε ^ (-1 : ℝ)) ≤ (1 / 2 : ℝ) * K := by
    nlinarith
  change P {ω | ¬ (1 / 32 : ℝ) * Real.logb 8 (ε ^ (-1 : ℝ)) ≤
    ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (8 : ℝ)⁻¹ ^ n) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)} ≤ _
  calc
    _ ≤ P {ω | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (8 : ℝ)⁻¹ ^ n) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ) <
        (1 / 2 : ℝ) * K} := measure_mono (fun _ h => lt_of_lt_of_le (not_le.mp h) hthreshold)
    _ ≤ _ := hcount
    _ ≤ _ := by
      have h := ofReal_exp_bound_le_rpow (by norm_num : (1 : ℝ) < 8) hε
        (by positivity : 0 ≤ 96 * Real.log 8) (by norm_num : (0 : ℝ) < 16) hCpos.le hK'
      have hexp : 96 * Real.log 8 / (16 * Real.log 8) = (6 : ℝ) := by field_simp; norm_num
      simpa only [hexp] using h

/-- Volume growth alone gives a universal eight-adic good-annulus prevalence
estimate for every admissible whole-plane realization. -/
theorem eightAdic_goodAnnulus_prevalence_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {b : ℝ} (hb : 0 < b) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      PolyHighProb P (fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
        (1 / 32 : ℝ) * Real.logb 8 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (8 : ℝ)⁻¹ ^ n) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)}) := by
  by_cases hex : ∃ (Ω : Type u) (m : MeasurableSpace Ω), letI := m
      ∃ (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc ∧
          IsLQGMeasureOfField P γ 0 hcirc μ
  · obtain ⟨Ω, m, P, hC, hcirc, μ, hgff, hμ⟩ := hex
    let : MeasurableSpace Ω := m
    exact exists_eightAdic_goodAnnulus_prevalence hgrowth hγ hγ2 hgff hμ hb
  · refine ⟨1 / 2, by norm_num, ?_⟩
    intro Ω m P hC hcirc μ hgff hμ
    exact False.elim (hex ⟨Ω, m, P, hC, hcirc, μ, hgff, hμ⟩)

end HarmonicBalls.Section6
