import HarmonicBalls.Proofs.Sec6.CriterionThreeUniversalLaw
import HarmonicBalls.Proofs.Sec6.AffineMeasureLaw

/-! # Measurability of subrange prevalence -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

/-- The good-radius count in the subrange is measurable in the measure,
provided the unit good-annulus event is measurable. -/
theorem measurable_subrange_goodAnnulus_count (ε : ℝ) (z : ℂ) (a b : ℝ)
    (hunit : MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ 1 0 a b}) :
    Measurable (fun μ : Measure ℂ =>
      ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z a b}.ncard : ℝ)) := by
  let f : ℕ → ℝ := fun k => (7 : ℝ)⁻¹ ^ k
  have hf : Function.Injective f :=
    pow_right_injective₀ (by norm_num : (0 : ℝ) < (7 : ℝ)⁻¹)
      (by norm_num : (7 : ℝ)⁻¹ ≠ 1)
  let S : Measure ℂ → Set ℕ := fun μ => {k |
    f k ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧ IsGoodAnnulus μ (f k) z a b}
  have hS : Measurable S := by
    apply measurable_setOfPred.comp
    apply measurable_pi_iff.mpr
    intro k
    apply measurableSet_setOfPred.mp
    by_cases h : f k ∈ Icc ε (ε ^ (3 / 4 : ℝ))
    · simp only [h, true_and]
      apply measurableSet_isGoodAnnulus_of_unit a b hunit
      dsimp [f]
      positivity
    · simp only [h, false_and]
      exact MeasurableSet.empty
  have hcount : Measurable (fun μ : Measure ℂ => ((S μ).ncard : ℝ)) := by
    exact Measurable.of_discrete.comp (measurable_ncard.comp hS)
  convert hcount using 1
  funext μ
  have heq : {r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z a b} = f '' S μ := by
    ext r
    constructor
    · rintro ⟨hr, ⟨k, rfl⟩, hg⟩
      exact ⟨k, ⟨hr, hg⟩, rfl⟩
    · rintro ⟨k, ⟨hr, hg⟩, rfl⟩
      exact ⟨hr, ⟨k, rfl⟩, hg⟩
  rw [heq, Set.ncard_image_of_injective _ hf]

/-- Subrange prevalence on the lattice is a measurable event in the measure. -/
theorem measurableSet_subrange_prevalence (ε a b c : ℝ)
    (hunit : MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ 1 0 a b}) :
    MeasurableSet {μ : Measure ℂ | ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z a b}.ncard : ℝ)} := by
  let z : ℤ → ℤ → ℂ := fun j k => ((ε / 100 : ℝ) : ℂ) *
    ((j : ℂ) + (k : ℂ) * Complex.I)
  let T : ℤ → ℤ → Set (Measure ℂ) := fun j k => {μ |
    z j k ∈ prevalenceGrid ε →
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ l : ℕ, r = (7 : ℝ)⁻¹ ^ l) ∧ IsGoodAnnulus μ r (z j k) a b}.ncard : ℝ)}
  have hT : ∀ j k, MeasurableSet (T j k) := by
    intro j k
    by_cases h : z j k ∈ prevalenceGrid ε
    · simpa only [T, h, true_implies] using
        measurableSet_le measurable_const (measurable_subrange_goodAnnulus_count ε (z j k) a b hunit)
    · simp only [T, h, false_implies, ofPred_true, MeasurableSet.univ]
  have heq : {μ : Measure ℂ | ∀ w ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r w a b}.ncard : ℝ)} =
      ⋂ j, ⋂ k, T j k := by
    ext μ
    simp only [mem_ofPred_eq, mem_iInter, T]
    constructor
    · intro h j k hz
      exact h (z j k) hz
    · intro h w hw
      obtain ⟨j, k, rfl⟩ := hw.2
      exact h j k hw
  rw [heq]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun k => hT j k

/-- Translation leaves the whole-plane subrange prevalence failure
probability unchanged, under the staged affine and coordinate-change laws. -/
theorem measure_subrange_prevalence_failure_translate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
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
  have hd := identDistrib_affineMeasure hgff hμ hAff hCC hγ hγ₂ (by norm_num : (1 : ℂ) ≠ 0) y
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

end HarmonicBalls.Section6
