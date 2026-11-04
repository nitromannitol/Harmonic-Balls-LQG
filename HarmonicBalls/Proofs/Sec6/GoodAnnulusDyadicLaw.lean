import HarmonicBalls.Proofs.Sec6.GoodAnnulusDyadicThreshold
import HarmonicBalls.Proofs.Sec6.RecenteredGoodAnnulusLocality
import HarmonicBalls.Proofs.Sec8.GoodEventPointPolarity

/-! # Good-annulus probabilities at dyadic scales

The imported Section 6 assembly uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- Good-annulus failure probabilities are independent of the centre and of
inverse dyadic scales under affine field invariance. -/
theorem badGoodAnnulus_probability_eq_unit_dyadic
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (n : ℕ) (z : ℂ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    P {ω | ¬ IsGoodAnnulus (μ ω) (dyadicScale n) z a b} =
      P {ω | ¬ IsGoodAnnulus (μ ω) 1 0 a b} := by
  let r := dyadicScale n
  let k : ℝ := (2 : ℝ) ^ n
  have hr : 0 < r := dyadicScale_pos n
  have hk : 0 < k := by dsimp [k]; positivity
  have hs : k * r = 1 := by
    dsimp [k, r]
    simpa only [zero_add, dyadicScale, pow_zero] using dyadicScale_shift n 0
  have hm := (measurableSet_isGoodAnnulus_of_pos r hr 0 a b ha).compl
  have hd := (identDistrib_normalizedPullback_dyadic hγ h hμ hAff n).measure_mem_eq hm
  have ht := (identDistrib_translateMeasure h hμ hAff z).measure_mem_eq hm
  change P {ω | ¬ IsGoodAnnulus (μ ω) r 0 a b} =
    P {ω | ¬ IsGoodAnnulus (normalizedPullbackMeasure γ 0 k (hcirc ω) (μ ω)) r 0 a b} at hd
  change P {ω | ¬ IsGoodAnnulus (μ ω) r 0 a b} =
    P {ω | ¬ IsGoodAnnulus (affineMeasure γ hcirc μ 1 z ω) r 0 a b} at ht
  have hd' : {ω | ¬ IsGoodAnnulus (normalizedPullbackMeasure γ 0 k (hcirc ω) (μ ω)) r 0 a b} =
      {ω | ¬ IsGoodAnnulus (μ ω) 1 0 a b} := by
    ext ω
    simp only [mem_ofPred_eq, normalizedPullbackMeasure]
    let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp
      (γ * (lqgQ γ * Real.log k + fieldCircleAverage 0 (hcirc ω) k 0)))⁻¹
    have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
    change ¬ IsGoodAnnulus (c • (μ ω).map (fun x : ℂ => k⁻¹ • x)) r 0 a b ↔
      ¬ IsGoodAnnulus (μ ω) 1 0 a b
    rw [isGoodAnnulus_smul _ _ _ _ _ hc0 hct,
      isGoodAnnulus_map_inv_smul_iff hk, smul_zero, hs]
  have ht' : {ω | ¬ IsGoodAnnulus (affineMeasure γ hcirc μ 1 z ω) r 0 a b} =
      {ω | ¬ IsGoodAnnulus (μ ω) r z a b} := by
    ext ω
    simp only [mem_ofPred_eq, isGoodAnnulus_affineMeasure_translate]
  rw [hd'] at hd
  rw [ht'] at ht
  exact ht.symm.trans hd

/-- A single threshold controls good-annulus failure at every inverse dyadic
scale and centre, uniformly over whole-plane realizations. -/
theorem exists_universal_goodAnnulus_probability_dyadic
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    (hAff₀ : WholePlaneGFFAffineInvariance P₀ hC₀ hcirc₀)
    {b : ℝ} (hb : 0 < b) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      WholePlaneGFFAffineInvariance P hC hcirc → ∀ (n : ℕ) (z : ℂ),
      P {ω | ¬ IsGoodAnnulus (μ ω) (dyadicScale n) z a b} ≤ ENNReal.ofReal (1 - p) := by
  let := h₀.isProbabilityMeasure
  have hmeas := h₀.aemeasurable_lqgMeasure hμ₀
  let ν := hmeas.mk μ₀
  have hν : Measurable ν := hmeas.measurable_mk
  have heq : μ₀ =ᵐ[P₀] ν := hmeas.ae_eq_mk
  have hae := ae_unit_goodAnnulus_threshold_of_volumeGrowth_dyadic hgrowth hγ hγ2 h₀ hμ₀ hAff₀ hb
  have hνae : ∀ᵐ ω ∂P₀, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (ν ω) 1 0 a b := by
    filter_upwards [hae, heq] with ω hω he
    simpa only [← he] using hω
  obtain ⟨a, ha, hbound⟩ := exists_goodAnnulus_threshold_of_measurable_events P₀
    (μ := ν) (fun n => (measurableSet_isGoodAnnulus_of_pos 1 (by norm_num) 0
      ((1 / 2 : ℝ) ^ (n + 1)) b (by positivity)).preimage hν) hνae hp
  refine ⟨a, ha, ?_⟩
  intro Ω _ P hC hcirc μ h hμ hAff n z
  rw [badGoodAnnulus_probability_eq_unit_dyadic hγ h hμ hAff n z ha.1 b]
  have hd := h₀.identDistrib_lqgMeasure_across_spaces h hμ₀ hμ
  have hevent := hd.measure_mem_eq (measurableSet_isGoodAnnulus_of_pos 1 (by norm_num) 0 a b ha.1).compl
  have hmod : P₀ {ω | ¬ IsGoodAnnulus (μ₀ ω) 1 0 a b} =
      P₀ {ω | ¬ IsGoodAnnulus (ν ω) 1 0 a b} := by
    apply measure_congr
    filter_upwards [heq] with ω hω
    simp only [hω]
  calc
    P {ω | ¬ IsGoodAnnulus (μ ω) 1 0 a b} =
        P₀ {ω | ¬ IsGoodAnnulus (μ₀ ω) 1 0 a b} := hevent.symm
    _ = P₀ {ω | ¬ IsGoodAnnulus (ν ω) 1 0 a b} := hmod
    _ ≤ ENNReal.ofReal (1 - p) := hbound

end HarmonicBalls.Section6
