import HarmonicBalls.Proofs.Sec6.CriterionThreeFromPrevalence
import HarmonicBalls.Proofs.Sec8.LQGUniversalMeasureLaw
import HarmonicBalls.Proofs.Sec8.GoodEventMeasurablePositive

/-! # Universality of the unit-scale third criterion -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

universe u

/-- Measurability of the unit good-annulus event implies measurability of
criterion three at every positive scale and center. -/
theorem measurableSet_criterionThree_of_unit_good (ρ : ℝ) (hρ : 0 < ρ)
    (x₀ : ℂ) (N₀ : ℕ) (a b c : ℝ)
    (hunit : MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ 1 0 a b}) :
    MeasurableSet {μ : Measure ℂ | VeryGoodCriterionThree μ ρ x₀ N₀ a b c} := by
  have h := measurableSet_veryGoodAnnulus_goodScales ρ hρ x₀ N₀ a b c (by
    intro n j k l
    apply measurableSet_isGoodAnnulus_of_unit a b hunit
    positivity)
  convert h using 1
  ext μ
  simp only [mem_ofPred_eq, VeryGoodCriterionThree, mem_inter_iff, scaledLattice]
  constructor
  · intro h n hn z hz hlat
    exact h n hn z ⟨hlat, hz⟩
  · intro h n hn z hz
    exact h n hn z hz.2 hz.1

/-- A prevalence estimate on one reference realization yields one starting
index valid for every realization of the same whole-plane LQG measure law. -/
theorem exists_universal_unit_criterionThree_probability
    {Ω₀ : Type u} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    {γ : ℝ} {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ}
    {μ₀ : Ω₀ → Measure ℂ} {a b c : ℝ} (hc : 0 < c)
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    (hprev : PolyHighProb P₀ fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ₀ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ 1 0 a b})
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
        P {ω | ¬ VeryGoodCriterionThree (μ ω) 1 0 N a b c} ≤ δ := by
  obtain ⟨N₀, hN₀, hbound⟩ :=
    exists_criterionThree_probability_of_subrange_prevalence P₀ hc hprev hδ
  refine ⟨N₀, hN₀, fun N hN Ω _ P hC hcirc μ h hμ => ?_⟩
  have hlaw := h₀.identDistrib_lqgMeasure_across_spaces h hμ₀ hμ
  have hmeas := (measurableSet_criterionThree_of_unit_good 1 (by norm_num) 0 N a b c hunit).compl
  have heq := hlaw.symm.measure_mem_eq hmeas
  exact heq ▸ hbound N hN

end HarmonicBalls.Section6
