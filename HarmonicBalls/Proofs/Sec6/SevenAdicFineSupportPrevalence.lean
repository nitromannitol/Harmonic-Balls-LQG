import HarmonicBalls.Proofs.Sec6.UniformGoodAnnulusFineSupport
import HarmonicBalls.Proofs.Sec6.CompactPhaseProbability
import HarmonicBalls.Proofs.Sec6.AffineInvarianceAssembly

/-! # Seven-adic prevalence from fine support

The imported annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter
open scoped ENNReal

universe u

/-- Volume growth gives a probability bound uniform over all seven-adic
radii. Only the countably many dyadic phases of these radii are needed. -/
theorem sevenAdic_goodAnnulus_probability_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b p : ℝ} (hb : 0 < b) (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ n : ℕ,
      P {ω | ¬ IsGoodAnnulus (μ ω) ((7 : ℝ)⁻¹ ^ n) 0 a b} ≤ ENNReal.ofReal (1 - p) := by
  classical
  let := h.isProbabilityMeasure
  have hex (n : ℕ) : ∃ (s : ℝ) (k : ℕ), s ∈ Ioc (1 / 2 : ℝ) 1 ∧
      (7 : ℝ)⁻¹ ^ n = s * dyadicScale k :=
    exists_dyadic_phase (pow_pos (by norm_num) n)
      (pow_le_one₀ (by norm_num) (by norm_num))
  choose s k hs heq using hex
  have hm := h.aemeasurable_lqgMeasure hμ
  let ν := hm.mk μ
  have hν : Measurable ν := hm.measurable_mk
  have hμν : μ =ᵐ[P] ν := hm.ae_eq_mk
  have hmeas (j : ℕ) : NullMeasurableSet
      {ω | ∀ r ∈ range s, IsGoodAnnulus (ν ω) r 0 ((1 / 2 : ℝ) ^ (j + 1)) b} P := by
    have hset : MeasurableSet {ω | ∀ i : ℕ,
        IsGoodAnnulus (ν ω) (s i) 0 ((1 / 2 : ℝ) ^ (j + 1)) b} := by
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i =>
        (measurableSet_isGoodAnnulus_of_pos (s i) (by linarith [(hs i).1]) 0
          ((1 / 2 : ℝ) ^ (j + 1)) b (by positivity)).preimage hν
    simpa only [forall_mem_range] using hset.nullMeasurableSet
  have hae : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      ∀ r ∈ range s, IsGoodAnnulus (ν ω) r 0 a b := by
    filter_upwards [ae_uniform_goodAnnulus_threshold_on_dyadic_phases hgrowth hγ hγ2 h hμ,
      hμν] with ω hω heqω
    obtain ⟨a, ha, hgood⟩ := hω 0 b hb
    refine ⟨a, ha, ?_⟩
    intro r hr
    obtain ⟨i, rfl⟩ := hr
    rw [← heqω]
    exact hgood (s i) ⟨(hs i).1.le, (hs i).2⟩
  obtain ⟨a, ha, hbound⟩ :=
    exists_uniform_goodAnnulus_threshold_of_measurable_events P hmeas hae hp
  refine ⟨a, ha, ?_⟩
  intro n
  have hmod : P {ω | ¬ IsGoodAnnulus (μ ω) (s n) 0 a b} =
      P {ω | ¬ IsGoodAnnulus (ν ω) (s n) 0 a b} := by
    apply measure_congr
    filter_upwards [hμν] with ω hω
    simp only [hω]
  rw [heq n, badGoodAnnulus_probability_eq_dyadic_orbit hγ h hμ
    (by linarith [(hs n).1]) (k n) ha.1 b, hmod]
  exact hbound (s n) (mem_range_self n)

/-- The whole-plane seven-adic good-annulus prevalence step follows from
volume growth alone. -/
theorem goodAnnuliSubRangeStep_of_volumeGrowth_fineSupport
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) : GoodAnnuliSubRangeStep.{u} := by
  apply goodAnnuliSubRangeStep_of_sevenAdic_reference_probability hgrowth
  intro γ hγ hγ2 b hb p hp Ω _ P hC hcirc μ h hμ
  exact sevenAdic_goodAnnulus_probability_of_volumeGrowth hgrowth hγ hγ2 h hμ hb.1 hp

/-- The whole-plane very-good prevalence step follows from volume growth. -/
theorem veryGoodAnnuliSubRangeStep_of_volumeGrowth_fineSupport
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) : VeryGoodAnnuliSubRangeStep.{u} :=
  veryGoodAnnuliSubRangeStep_of_goodPrevalence hgrowth
    (goodAnnuliSubRangeStep_of_volumeGrowth_fineSupport hgrowth)

/-- Lemma 6.3 from volume growth and staged zero-strength LQG existence. -/
theorem manyGoodAnnuliStmt_of_volumeGrowth_zero_existence
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc) : ManyGoodAnnuliStmt.{u} := by
  apply manyGoodAnnuliStmt_of_literature
    (goodAnnuliSubRangeStep_of_volumeGrowth_fineSupport hgrowth) hE0
  intro Ω _ P γ hC hcirc
  exact lqgMeasureWeylScaling Ω P γ 0 hC hcirc

/-- Lemma 6.6 from volume growth and staged zero-strength LQG existence. -/
theorem manyVeryGoodAnnuliStmt_of_volumeGrowth_zero_existence
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc) : ManyVeryGoodAnnuliStmt.{u} := by
  apply manyVeryGoodAnnuliStmt_of_literature
    (veryGoodAnnuliSubRangeStep_of_volumeGrowth_fineSupport hgrowth) hE0
  intro Ω _ P γ hC hcirc
  exact lqgMeasureWeylScaling Ω P γ 0 hC hcirc

/-- Proposition 6.2 from volume growth and staged zero-strength LQG existence. -/
theorem harnackTypeComponentStmt_of_volumeGrowth_zero_existence
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc) : HarnackTypeComponentStmt.{u} := by
  apply harnackTypeComponentStmt_of_goodPrevalence_of_translation hgrowth
    (goodAnnuliSubRangeStep_of_volumeGrowth_fineSupport hgrowth) ?_ hE0
  intro Ω _ P hC hcirc
  exact wholePlaneGFFAffineInvariance_proved P hC hcirc

/-- Proposition 6.1 from volume growth and staged zero-strength LQG existence. -/
theorem harnackTypeEstimateStmt_of_volumeGrowth_zero_existence
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc) : HarnackTypeEstimateStmt.{u} := by
  apply harnackTypeEstimateStmt_of_goodPrevalence_of_translation hgrowth
    (goodAnnuliSubRangeStep_of_volumeGrowth_fineSupport hgrowth) ?_ hE0
  intro Ω _ P hC hcirc
  exact wholePlaneGFFAffineInvariance_proved P hC hcirc

end HarmonicBalls.Section6
