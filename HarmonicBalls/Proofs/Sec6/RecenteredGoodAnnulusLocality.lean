import HarmonicBalls.Proofs.Sec6.AnnularCenteredExhaustion
import HarmonicBalls.Proofs.Sec6.GoodPrevalenceAffine

/-! # Recentered good-annulus locality

The imported annulus iteration uses Leonardo Bonanno's proof of the
Gwynne–Miller lemma in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
The affine GFF and coordinate-change inputs remain staged assumptions.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter MarkovProcess
open scoped ENNReal NNReal Topology

universe u

/-- Translating and renormalizing an LQG measure preserves its good-annulus
condition at the translated center. -/
theorem isGoodAnnulus_affineMeasure_translate
    {Ω : Type*} (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (r : ℝ) (z : ℂ) (a b : ℝ) (ω : Ω) :
    IsGoodAnnulus (affineMeasure γ hcirc μ 1 z ω) r 0 a b ↔
      IsGoodAnnulus (μ ω) r z a b := by
  unfold affineMeasure
  rw [isGoodAnnulus_smul _ _ _ _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
    ENNReal.ofReal_ne_top]
  simpa only [div_one, sub_eq_add_neg, add_neg_cancel] using
    isGoodAnnulus_map_add_iff (-z) (μ ω) r z a b

/-- The original good-annulus event is local in the recentered field. The
LQG regularity and Brownian point-avoidance inputs are explicit. -/
theorem isFieldMeasurableModConst_goodAnnulus_recentered
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) {r : ℝ} (hr : 0 < r) (z : ℂ)
    {a : ℝ} (ha : 0 < a) (b : ℝ)
    (hatom : LQGMeasureNonatomic P γ 0 (affinePairing hC hcirc 1 z)
      (affineCircle hcirc 1 z))
    (hpolar : ∀ u ∈ sphere (0 : ℂ) (4 * r), ∀ x ∈ annulus 0 (3 * r) (5 * r), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    IsFieldMeasurableModConst P 0 (affinePairing hC hcirc 1 z)
      (annulus 0 (3 * r) (5 * r)) {ω | IsGoodAnnulus (μ ω) r z a b} := by
  let ν := affineMeasure γ hcirc μ 1 z
  have hs : IsWholePlaneGFF P (affinePairing hC hcirc 1 z) (affineCircle hcirc 1 z) :=
    hAff hgff 1 one_ne_zero z
  have hν : IsLQGMeasureOfField P γ 0 (affineCircle hcirc 1 z) ν :=
    isLQGMeasureOfField_affine hCC hgff hγ hγ2 hμ one_ne_zero z
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hreg := ae_lqg_goodAnnulus_regular hfull hγ hγ2 hQ hs hν hatom hr 0 ha
  have hfinite : ∀ᵐ ω ∂P, ν ω (annulus 0 (3 * r) (5 * r)) ≠ ∞ := by
    filter_upwards [hreg] with ω hω
    exact hω.2.1
  have hpositive : ∀ᵐ ω ∂P, 0 < ν ω (annulus 0 (3 * r) (5 * r)) := by
    filter_upwards [hreg] with ω hω
    exact bot_lt_iff_ne_bot.mpr ((mul_ne_zero_iff.mp hω.2.2.ne').2)
  have hatom' : ∀ᵐ ω ∂P, ∀ x : ℂ, ν ω {x} = 0 := by
    filter_upwards [hreg] with ω hω
    exact hω.1
  have hd := identDistrib_affineMeasure hgff hμ hAff hCC hγ hγ2 (a := 1) one_ne_zero z
  have hfront0 := ae_lqg_annulus_frontier_eq_zero_of_affine hgff hμ hAff hCC hγ hγ2
    0 (show 0 < 3 * r by positivity) (show 0 < 5 * r by positivity)
  have hmeas : MeasurableSet {m : Measure ℂ | m (frontier (annulus 0 (3 * r) (5 * r))) = 0} :=
    measurableSet_eq_fun (Measure.measurable_coe isClosed_frontier.measurableSet) measurable_const
  have hfront : ∀ᵐ ω ∂P, ν ω (frontier (annulus 0 (3 * r) (5 * r))) = 0 :=
    hd.ae_snd hmeas hfront0
  have hlocal := isFieldMeasurableModConst_goodAnnulus_of_null_frontier hs hν hr 0 ha b
    hatom' hfinite hpositive hpolar hfront
  obtain ⟨A, hA, hAe⟩ := hlocal
  refine ⟨A, hA, ?_⟩
  filter_upwards [hAe] with ω hω
  simpa only [ν, mem_ofPred_eq, isGoodAnnulus_affineMeasure_translate γ hcirc μ r z a b ω] using hω

/-- Good-annulus prevalence follows from the unit threshold and point
avoidance at positive radii, with the staged LQG regularity and affine laws. -/
theorem goodAnnuliSubRangeStep_of_ae_unit_and_point_avoidance
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
    (hpolar : ∀ (r : ℝ), 0 < r → ∀ v ∈ sphere (0 : ℂ) (4 * r),
      ∀ x ∈ annulus 0 (3 * r) (5 * r), x ≠ v →
      ∀ᵐ path ∂(planarBrownianMotion v), ∀ t : ℝ≥0, path t ≠ x)
    (hunit : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type u) [MeasurableSpace Ω]
      (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc →
      IsLQGMeasureOfField P γ 0 hcirc μ → ∀ b ∈ Ioo (0 : ℝ) 1,
      ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (μ ω) 1 0 a b) :
    GoodAnnuliSubRangeStep.{u} := by
  apply goodAnnuliSubRangeStep_of_ae_unit_and_locality hfull hatom hAff hCC
    (hpolar 1 (by norm_num)) hunit
  intro γ hγ hγ2 Ω _ P hC hcirc μ hgff hμ a ha b hb z n
  have hr : 0 < (7 : ℝ)⁻¹ ^ n := pow_pos (by norm_num) n
  exact isFieldMeasurableModConst_goodAnnulus_recentered hfull hgff hμ
    (hAff Ω P hC hcirc) (hCC Ω P γ hC hcirc) hγ hγ2 hr z ha.1 b
    (hatom Ω P γ (affinePairing hC hcirc 1 z) (affineCircle hcirc 1 z))
    (hpolar _ hr)

end HarmonicBalls.Section6
