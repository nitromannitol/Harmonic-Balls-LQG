import HarmonicBalls.Proofs.Sec6.UnitDiscRootedPolynomialTail

/-! # Weighted unit-disc rooted annulus tails

The countable-centre iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- A weight bounded above and away from zero has positive finite mass on the
unit disc whenever the LQG measure has positive finite unit-disc mass. -/
theorem ae_weighted_unitDisc_lqg_mass_pos_ne_top
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (w : ℂ → ℝ≥0∞) {c C : ℝ≥0∞} (hc : c ≠ 0) (hC : C ≠ ∞)
    (hwlower : ∀ z, c ≤ w z) (hwupper : ∀ z, w z ≤ C) :
    ∀ᵐ ω ∂P, ((μ ω).withDensity w) (ball 0 1) ≠ 0 ∧
      ((μ ω).withDensity w) (ball 0 1) ≠ ∞ := by
  filter_upwards [ae_unitDisc_lqg_mass_pos_ne_top hgrowth hγ hγ2 h hμ] with ω hm
  have hlo : (μ ω).withDensity (fun _ => c) ≤ (μ ω).withDensity w :=
    withDensity_mono (Filter.Eventually.of_forall hwlower)
  have hhi : (μ ω).withDensity w ≤ (μ ω).withDensity (fun _ => C) :=
    withDensity_mono (Filter.Eventually.of_forall hwupper)
  have hlo' := hlo (ball (0 : ℂ) 1)
  have hhi' := hhi (ball (0 : ℂ) 1)
  rw [withDensity_const, Measure.smul_apply, smul_eq_mul] at hlo' hhi'
  exact ⟨ne_zero_of_lt (lt_of_lt_of_le (ENNReal.mul_pos hc hm.1) hlo'),
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hC hm.2) hhi'⟩

/-- Weighted LQG sampling from the unit disc has polynomial good-annulus
count tails, uniformly in weights with positive finite normalization. -/
theorem exists_weighted_unitDisc_lqg_root_goodAnnuli_polynomial_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (q β : ℝ) (hq : 0 < q) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ, 0 < s → ∃ C : ℝ, 0 < C ∧
    ∀ (w : ℂ → ℝ≥0∞) (hw : Measurable w),
      (∀ᵐ ω ∂P, ((μ ω).withDensity w) (ball 0 1) ≠ 0 ∧
        ((μ ω).withDensity w) (ball 0 1) ≠ ∞) →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball w hw)
        {p | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2 a (b + 1)}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤ ENNReal.ofReal (C * ε ^ q) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  obtain ⟨a, ha, ht⟩ := exists_rooted_unitDisc_goodAnnuli_polynomial_tail
    hgrowth hγ hγ2 h hμ hb q β hq hβ
  refine ⟨a, ha, ?_⟩
  intro s hs
  obtain ⟨C, hC, htail⟩ := ht s hs
  refine ⟨C, hC, ?_⟩
  intro w hw hmass ε hε hε1 hlog
  let hm := h.aemeasurable_lqgMeasure hμ
  let κ := weightedRestrictionKernel P μ hm (ball 0 1) measurableSet_ball w hw
  have hk : ∀ᵐ ω ∂P, κ ω univ = 1 := by
    filter_upwards [ae_weightedRestrictionKernel_eq P μ hm (ball 0 1) measurableSet_ball w hw,
      hmass] with ω he hh
    rw [he]
    simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hh.1 hh.2
  have hac : ∀ᵐ ω ∂P, κ ω ≪ μ ω := by
    filter_upwards [ae_weightedRestrictionKernel_eq P μ hm (ball 0 1) measurableSet_ball w hw] with ω he
    rw [he, normalizedRestriction]
    exact Measure.smul_absolutelyContinuous.trans
      (Measure.absolutelyContinuous_restrict.trans (withDensity_absolutelyContinuous _ _))
  calc
    _ ≤ (P ⊗ₘ κ) {p | p.2 ∈ ball (0 : ℂ) 1 ∧
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2 a (b + 1)}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} := by
      apply measure_mono_ae
      filter_upwards [ae_mem_weightedRestriction_compProd P μ hm (ball 0 1)
        measurableSet_ball w hw] with p hp hpE
      exact ⟨hp, hpE⟩
    _ ≤ _ := htail κ hk hac ε hε hε1 hlog

end HarmonicBalls.Section6
