import HarmonicBalls.Proofs.Sec6.PhaseCriterionThreeProbability
import HarmonicBalls.Proofs.Sec6.LQGTranslationCovariance
import HarmonicBalls.Proofs.Sec6.SubrangePrevalenceMeasurable
import HarmonicBalls.Proofs.Sec8.UniversalPhaseProbability
import HarmonicBalls.Proofs.Sec6.DyadicMeasureScalingLaw
import HarmonicBalls.Proofs.Sec6.CriterionThreeScaling

/-! # Phase criterion from translation covariance

The imported annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. Translation covariance
follows from the LQG limit, with affine field invariance kept explicit.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- Translation preserves the subrange prevalence probability under affine
field invariance. -/
theorem measure_subrange_prevalence_failure_translate_of_affine
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (ε a b c : ℝ) (y : ℂ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) :
    P {ω | ¬ ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)} =
    P {ω | ¬ ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
            IsGoodAnnulus ((μ ω).map (fun w : ℂ => w + -y)) r z a b}.ncard : ℝ)} := by
  have hd := identDistrib_translateMeasure hgff hμ hAff y
  have hm := (measurableSet_subrange_prevalence ε a b c hunit).compl
  have heq := hd.measure_mem_eq hm
  have htransport (ω : Ω) (r : ℝ) (z : ℂ) :
      IsGoodAnnulus (affineMeasure γ hcirc μ 1 y ω) r z a b ↔
        IsGoodAnnulus ((μ ω).map (fun w : ℂ => w + -y)) r z a b := by
    simp only [affineMeasure, div_one, sub_eq_add_neg]
    apply isGoodAnnulus_smul
    · positivity
    · exact ENNReal.ofReal_ne_top
  change P {ω | ¬ ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)} =
    P {ω | ¬ ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
            IsGoodAnnulus (affineMeasure γ hcirc μ 1 y ω) r z a b}.ncard : ℝ)} at heq
  simpa only [htransport] using heq


/-- A subrange prevalence estimate gives a phase-uniform unit criterion
without assuming a general coordinate-change law. -/
theorem exists_phase_uniform_unit_criterionThree_probability_of_affine
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {a b c : ℝ} (hc : 0 < c)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hprev : PolyHighProb P fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ (x : ℂ) (phase : ℕ → ℂ),
      P {ω | ¬ ∀ n : ℕ, N ≤ n → ∀ z ∈ annulus x (1 / 2) 1,
        z - phase n ∈ scaledLattice (dyadicScale n / 100) →
        c * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc (dyadicScale n * 1) (Real.sqrt (dyadicScale n) * 1) ∧
            (∃ k : ℕ, 1 ≤ k ∧ r = 1 * (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)} ≤ δ := by
  obtain ⟨N₀, hN₀, hbound⟩ := exists_uniform_dyadic_failure_tail_bound P hprev hδ
  refine ⟨N₀, hN₀, fun N hN x phase => ?_⟩
  have hpos (n : ℕ) : 0 < dyadicScale n / 100 := by
    unfold dyadicScale
    positivity
  choose y hy hxy using fun n : ℕ => exists_phase_scaledLattice_dist_lt x (phase n) (hpos n)
  let F : ℕ → Set Ω := fun n => {ω | ∀ z ∈ prevalenceGrid (dyadicScale n),
    c * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
      ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
        (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus ((μ ω).map (fun w : ℂ => w + -(y n))) r z a b}.ncard : ℝ)}
  have hF : ∀ n, P (F n)ᶜ ≤ P {ω | ∀ z ∈ prevalenceGrid ((2 : ℝ)⁻¹ ^ n),
      c * Real.logb 7 (((2 : ℝ)⁻¹ ^ n) ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ((2 : ℝ)⁻¹ ^ n) (((2 : ℝ)⁻¹ ^ n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)}ᶜ := by
    intro n
    have heq := measure_subrange_prevalence_failure_translate_of_affine hgff hμ hAff
      (dyadicScale n) a b c (y n) hunit
    simpa only [F, dyadicScale, compl_ofPred] using heq.symm.le
  calc P {ω | ¬ ∀ n : ℕ, N ≤ n → ∀ z ∈ annulus x (1 / 2) 1,
        z - phase n ∈ scaledLattice (dyadicScale n / 100) →
        c * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc (dyadicScale n * 1) (Real.sqrt (dyadicScale n) * 1) ∧
            (∃ k : ℕ, 1 ≤ k ∧ r = 1 * (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)} ≤
      P {ω | ∀ n : ℕ, N ≤ n → ω ∈ F n}ᶜ := by
        apply measure_mono
        intro ω hbad hgood
        apply hbad
        intro n hn
        exact phase_criterionThree_count_of_translated_subrange_prevalence hc
          (hN₀.trans (hN.trans hn)) (hy n) (hxy n) (hgood n hn)
    _ ≤ δ := hbound N hN F hF


/-- Phase-uniform prevalence expressed using the phase criterion. -/
theorem exists_phaseVeryGoodCriterionThree_probability_of_affine
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {a b c : ℝ} (hc : 0 < c)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hprev : PolyHighProb P fun ε => {ω | ∀ z ∈ Section6.prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ (x : ℂ) (phase : ℕ → ℂ),
      P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) 1 x N a b c phase} ≤ δ := by
  obtain ⟨N₀, hN₀, hbound⟩ := Section6.exists_phase_uniform_unit_criterionThree_probability_of_affine
    P hc hgff hμ hAff hprev hunit hδ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN x phase
  simpa only [PhaseVeryGoodCriterionThree, mul_one] using hbound N hN x phase


/-- A reference prevalence estimate bounds every whole-plane realization. -/
theorem exists_universal_phaseCriterion_probability_of_affine
    {Ξ : Type u} [MeasurableSpace Ξ] (P₀ : Measure Ξ) {γ a b c : ℝ}
    (hc : 0 < c)
    {hC₀ : Ξ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ξ → ℝ → ℂ → ℝ} {ν₀ : Ξ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hν₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ ν₀)
    (hAff₀ : WholePlaneGFFAffineInvariance P₀ hC₀ hcirc₀)
    (hprev : PolyHighProb P₀ fun ε => {ω | ∀ z ∈ Section6.prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (ν₀ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ν : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc ν → ∀ q : ℂ,
        P {ω | ¬ PhaseVeryGoodCriterionThree (ν ω) 1 0 N a b c (fun _ => q)} ≤ δ := by
  obtain ⟨N₀, hN₀, hbound⟩ := exists_phaseVeryGoodCriterionThree_probability_of_affine
    P₀ hc h₀ hν₀ hAff₀ hprev hunit hδ
  refine ⟨N₀, hN₀, fun N hN Ω _ P hC hcirc ν h hν q => ?_⟩
  have hlaw := h₀.identDistrib_lqgMeasure_across_spaces h hν₀ hν
  have heq := hlaw.symm.measure_mem_eq (measurableSet_phaseCriterion_fixed N a b c q hunit).compl
  exact heq ▸ hbound N hN 0 (fun _ => q)

/-- Criterion-three failure at the origin has the same probability at every
inverse dyadic scale as at unit scale. -/
theorem measure_criterionThree_failure_dyadic_of_affine
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (n N : ℕ) (a b c : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) :
    P {ω | ¬ VeryGoodCriterionThree (μ ω) (dyadicScale n) 0 N a b c} =
      P {ω | ¬ VeryGoodCriterionThree (μ ω) 1 0 N a b c} := by
  let k : ℝ := (2 : ℝ) ^ n
  have hk : 0 < k := by dsimp [k]; positivity
  have hs : k * dyadicScale n = 1 := by
    dsimp [k]
    simpa only [zero_add, dyadicScale, pow_zero] using dyadicScale_shift n 0
  have hd := identDistrib_normalizedPullback_dyadic hγ hgff hμ hAff n
  have hm := (measurableSet_criterionThree_of_unit_good (dyadicScale n)
    (dyadicScale_pos n) 0 N a b c hunit).compl
  have heq := hd.measure_mem_eq hm
  have htransport (ω : Ω) :
      VeryGoodCriterionThree (normalizedPullbackMeasure γ 0 k (hcirc ω) (μ ω))
        (dyadicScale n) 0 N a b c ↔ VeryGoodCriterionThree (μ ω) 1 0 N a b c := by
    unfold normalizedPullbackMeasure
    rw [criterionThree_smul _ _ _ _ _ _ _ (by positivity) ENNReal.ofReal_ne_top,
      criterionThree_map_inv_smul _ hk, hs]
  change P {ω | ¬ VeryGoodCriterionThree (μ ω) (dyadicScale n) 0 N a b c} =
    P {ω | ¬ VeryGoodCriterionThree
      (normalizedPullbackMeasure γ 0 k (hcirc ω) (μ ω)) (dyadicScale n) 0 N a b c} at heq
  simpa only [htransport] using heq

/-- One reference prevalence estimate controls criterion-three failure at
the origin at every inverse dyadic scale and for every whole-plane realization. -/
theorem exists_universal_dyadic_criterionThree_probability_of_affine
    {Ξ : Type u} [MeasurableSpace Ξ] (P₀ : Measure Ξ) {γ a b c : ℝ}
    (hγ : 0 < γ) (hc : 0 < c)
    {hC₀ : Ξ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ξ → ℝ → ℂ → ℝ} {ν₀ : Ξ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hν₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ ν₀)
    (hAff₀ : WholePlaneGFFAffineInvariance P₀ hC₀ hcirc₀)
    (hprev : PolyHighProb P₀ fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (ν₀ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ν : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc ν →
        WholePlaneGFFAffineInvariance P hC hcirc → ∀ n : ℕ,
        P {ω | ¬ VeryGoodCriterionThree (ν ω) (dyadicScale n) 0 N a b c} ≤ δ := by
  obtain ⟨N₀, hN₀, hbound⟩ := exists_universal_phaseCriterion_probability_of_affine
    P₀ hc h₀ hν₀ hAff₀ hprev hunit hδ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN Ω _ P hC hcirc ν h hν hAff n
  rw [measure_criterionThree_failure_dyadic_of_affine hγ h hν hAff n N a b c hunit]
  simpa only [phaseVeryGoodCriterionThree_zero] using hbound N hN Ω P hC hcirc ν h hν 0


end HarmonicBalls.Section6
