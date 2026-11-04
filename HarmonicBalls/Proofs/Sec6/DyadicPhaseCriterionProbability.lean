import HarmonicBalls.Proofs.Sec6.PhaseCriterionTranslationCovariance
import HarmonicBalls.Proofs.Sec6.VeryGoodUnionBound
import HarmonicBalls.Proofs.Sec8.GoodEventPointPolarity

/-! # Dyadic criterion-three bounds at arbitrary deterministic centres

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
The shifted phase is retained when changing coordinates.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- A fixed common phase gives a measurable criterion at every positive radius. -/
theorem measurableSet_phaseCriterion_fixed_scale (ρ : ℝ) (hρ : 0 < ρ)
    (N : ℕ) (a b c : ℝ) (q : ℂ)
    (hunit : MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ 1 0 a b}) :
    MeasurableSet {μ : Measure ℂ |
      PhaseVeryGoodCriterionThree μ ρ 0 N a b c (fun _ => q)} := by
  have hm := (measurableSet_criterionThree_of_unit_good ρ hρ (-q) N a b c hunit).preimage
    (measurable_measure_map_sub q)
  convert hm using 1
  ext μ
  have h := phaseVeryGoodCriterionThree_map_add μ ρ 0 (-q) N a b c (fun _ => q)
  simpa only [add_neg_cancel, zero_add, ← sub_eq_add_neg,
    phaseVeryGoodCriterionThree_zero, mem_ofPred_eq, mem_preimage, zero_sub] using h.symm

/-- The third criterion is unchanged by a positive finite measure scalar. -/
theorem phaseCriterion_smul (ν : Measure ℂ) (ρ : ℝ) (x : ℂ) (N : ℕ)
    (a b c : ℝ) (phase : ℕ → ℂ) {d : ℝ≥0∞} (hd : d ≠ 0) (hdt : d ≠ ∞) :
    PhaseVeryGoodCriterionThree (d • ν) ρ x N a b c phase ↔
      PhaseVeryGoodCriterionThree ν ρ x N a b c phase := by
  simp only [PhaseVeryGoodCriterionThree, isGoodAnnulus_smul ν _ _ _ _ hd hdt]

/-- Translation and dyadic dilation preserve the third criterion with its
corresponding lattice phase. -/
theorem measure_criterionThree_failure_dyadic_center_of_affine
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (n N : ℕ) (z : ℂ) (a b c : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) :
    P {ω | ¬ VeryGoodCriterionThree (μ ω) (dyadicScale n) z N a b c} =
      P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) 1 0 N a b c
        (fun _ => (2 : ℝ) ^ n • (-z))} := by
  let k : ℝ := (2 : ℝ) ^ n
  have hk : 0 < k := by dsimp [k]; positivity
  have hs : k * dyadicScale n = 1 := by
    dsimp [k]
    simpa only [zero_add, dyadicScale, pow_zero] using dyadicScale_shift n 0
  have ht := identDistrib_translateMeasure hgff hμ hAff z
  have hmeas := (measurableSet_phaseCriterion_fixed_scale (dyadicScale n)
    (dyadicScale_pos n) N a b c (-z) hunit).compl
  have heqt := ht.measure_mem_eq hmeas
  have htranslate (ω : Ω) :
      PhaseVeryGoodCriterionThree (affineMeasure γ hcirc μ 1 z ω)
        (dyadicScale n) 0 N a b c (fun _ => -z) ↔
      VeryGoodCriterionThree (μ ω) (dyadicScale n) z N a b c := by
    simp only [affineMeasure, div_one, sub_eq_add_neg]
    rw [phaseCriterion_smul _ _ _ _ _ _ _ _ (by positivity) ENNReal.ofReal_ne_top]
    have h := phaseVeryGoodCriterionThree_map_add (μ ω) (dyadicScale n) z (-z)
      N a b c (fun _ => 0)
    simpa only [add_neg_cancel, zero_add, phaseVeryGoodCriterionThree_zero] using h
  have htrans : P {ω | ¬ VeryGoodCriterionThree (μ ω) (dyadicScale n) z N a b c} =
      P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) (dyadicScale n) 0 N a b c (fun _ => -z)} := by
    change P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) (dyadicScale n) 0 N a b c
          (fun _ => -z)} =
        P {ω | ¬ PhaseVeryGoodCriterionThree (affineMeasure γ hcirc μ 1 z ω)
          (dyadicScale n) 0 N a b c (fun _ => -z)} at heqt
    simpa only [htranslate] using heqt.symm
  rw [htrans]
  have hd := identDistrib_normalizedPullback_dyadic hγ hgff hμ hAff n
  have heqd := hd.measure_mem_eq hmeas
  have hscale (ω : Ω) :
      PhaseVeryGoodCriterionThree (normalizedPullbackMeasure γ 0 k (hcirc ω) (μ ω))
        (dyadicScale n) 0 N a b c (fun _ => -z) ↔
      PhaseVeryGoodCriterionThree (μ ω) 1 0 N a b c (fun _ => k • (-z)) := by
    unfold normalizedPullbackMeasure
    rw [phaseCriterion_smul _ _ _ _ _ _ _ _ (by positivity) ENNReal.ofReal_ne_top,
      phaseVeryGoodCriterionThree_map_inv_smul _ hk, hs, smul_zero]
  change P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) (dyadicScale n) 0 N a b c (fun _ => -z)} =
    P {ω | ¬ PhaseVeryGoodCriterionThree (normalizedPullbackMeasure γ 0 k (hcirc ω) (μ ω))
      (dyadicScale n) 0 N a b c (fun _ => -z)} at heqd
  simpa only [hscale] using heqd

/-- A reference prevalence estimate gives one index controlling the third
criterion at every deterministic centre and inverse dyadic radius. -/
theorem exists_universal_dyadic_criterionThree_center_probability_of_affine
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
        WholePlaneGFFAffineInvariance P hC hcirc → ∀ (n : ℕ) (z : ℂ),
        P {ω | ¬ VeryGoodCriterionThree (ν ω) (dyadicScale n) z N a b c} ≤ δ := by
  obtain ⟨N₀, hN₀, hbound⟩ := exists_universal_phaseCriterion_probability_of_affine
    P₀ hc h₀ hν₀ hAff₀ hprev hunit hδ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN Ω _ P hC hcirc ν hgff hν hAff n z
  rw [measure_criterionThree_failure_dyadic_center_of_affine hγ hgff hν hAff n N z a b c hunit]
  exact hbound N hN Ω P hC hcirc ν hgff hν ((2 : ℝ) ^ n • (-z))

/-- The three very-good criteria hold with high probability at each prescribed
centre and inverse dyadic radius, uniformly over whole-plane realizations. -/
theorem exists_universal_dyadic_veryGood_probability_of_affine
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ξ : Type u} [MeasurableSpace Ξ] (P₀ : Measure Ξ) {γ β a b c : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β) (hc : 0 < c)
    {hC₀ : Ξ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ξ → ℝ → ℂ → ℝ} {ν₀ : Ξ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hν₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ ν₀)
    (hAff₀ : WholePlaneGFFAffineInvariance P₀ hC₀ hcirc₀)
    (hprev : PolyHighProb P₀ fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (ν₀ ω) r z a b}.ncard : ℝ)})
    (ha : 0 < a)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ν : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc ν →
        WholePlaneGFFAffineInvariance P hC hcirc → ∀ (n : ℕ) (z : ℂ),
        P {ω | ¬ IsVeryGoodAnnulus (ν ω) β (dyadicScale n) z N
          a b C₁m C₁p C₂m C₂p c} ≤ δ + δ + δ := by
  have hunit := measurableSet_isGoodAnnulus_of_pos 1 (by norm_num) 0 a b ha
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, hsize⟩ :=
    exists_universal_wholePlane_size_windows_dyadic hgrowth hγ hγ₂ hβ P₀ h₀ hν₀ hδ
  obtain ⟨N₀, hN₀, hthree⟩ :=
    exists_universal_dyadic_criterionThree_center_probability_of_affine
      P₀ hγ hc h₀ hν₀ hAff₀ hprev hunit hδ
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, ?_⟩
  intro N hN Ω _ P hC hcirc ν hgff hν hAff n z
  have hs := hsize Ω P hC hcirc ν hgff hν hAff n z
  exact (measure_not_veryGoodAnnulus_le P ν β (dyadicScale n) z N
    a b C₁m C₁p C₂m C₂p c).trans
      (add_le_add (add_le_add hs.1 hs.2) (hthree N hN Ω P hC hcirc ν hgff hν hAff n z))

end HarmonicBalls.Section6
