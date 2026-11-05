import HarmonicBalls.Proofs.Sec6.CountableNearbyAnnulusSelectors
import HarmonicBalls.Proofs.Sec8.RootedSamplingProbability

/-! # Countable nearby-annulus bounds under normalized rooting

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- An almost surely normalized sampling kernel preserves the field law under
projection from the composition-product rooted law. -/
theorem measurePreserving_fst_compProd_of_ae_normalized
    {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (P : Measure Ω) [SFinite P] (κ : Kernel Ω Z) [IsSFiniteKernel κ]
    (hκ : ∀ᵐ ω ∂P, κ ω univ = 1) :
    MeasurePreserving Prod.fst (P ⊗ₘ κ) P := by
  refine ⟨measurable_fst, ?_⟩
  ext S hS
  rw [Measure.map_apply measurable_fst hS]
  rw [show Prod.fst ⁻¹' S = S ×ˢ univ from by ext x; simp]
  rw [Measure.compProd_apply_prod hS MeasurableSet.univ]
  rw [lintegral_congr_ae (ae_restrict_of_ae hκ)]
  simp

/-- A normalized weighted restriction samples a root without changing the
field marginal. -/
theorem measurePreserving_fst_weightedRestriction_compProd
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hmass : ∀ᵐ ω ∂P, ((μ ω).withDensity w) B ≠ 0 ∧
      ((μ ω).withDensity w) B ≠ ∞) :
    MeasurePreserving Prod.fst (P ⊗ₘ weightedRestrictionKernel P μ hμ B hB w hw) P := by
  apply measurePreserving_fst_compProd_of_ae_normalized
  filter_upwards [ae_weightedRestrictionKernel_eq P μ hμ B hB w hw, hmass] with ω he hm
  rw [he]
  simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hm.1 hm.2

/-- The count-tail estimate for all selectors from a prescribed countable
centre family also holds under any normalized composition-product root law.
The selectors can depend on the sampled root. -/
theorem exists_rooted_countable_nearby_goodAnnuli_selected_count_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {Z : Type*} [MeasurableSpace Z] (κ : Kernel Ω Z) [IsSFiniteKernel κ]
    (hκ : ∀ᵐ ω ∂P, κ ω univ = 1)
    {b : ℝ} (hb : 0 < b) (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ (x : ℂ) (z : ℝ → ℕ → ℂ), (∀ r i, z r i ∈ ball 0 ((1 : ℝ) / 100)) →
    ∀ s : ℝ, 0 < s → ∀ ε : ℝ, 0 < ε →
      16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      (P ⊗ₘ κ) {p | ∃ f : ℝ → ℕ,
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) (x + (s * r) • z (s * r) (f r)) a b}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤
      ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) := by
  let := h.isProbabilityMeasure
  obtain ⟨a, ha, C, hC, htail⟩ :=
    exists_countable_nearby_goodAnnuli_selected_count_tail hgrowth hγ hγ2 h hμ hb α β hα hβ
  refine ⟨a, ha, C, hC, ?_⟩
  intro x z hz s hs ε hε ht
  have hnm := (h.aemeasurable_lqgMeasure hμ).nullMeasurableSet_preimage
    (measurableSet_exists_nearby_selected_count_lt x z (b := b)
      (c := (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))) hs hε ha.1)
  have hp := measurePreserving_fst_compProd_of_ae_normalized P κ hκ
  have heq := hp.measure_preimage hnm
  simp only [preimage_ofPred_eq] at heq
  rw [heq]
  exact htail x z hz s hs ε hε ht

end HarmonicBalls.Section6
