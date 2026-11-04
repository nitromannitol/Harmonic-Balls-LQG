import HarmonicBalls.Proofs.Sec8.VeryGoodLocality
import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-! # Measurability of the good-scale count

The radii in the third very-good-annulus condition form a countable geometric
sequence. Measurability of each good-annulus event therefore suffices for the
count and the entire third condition to be measurable.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- The number of good radii in a geometric sequence is measurable in the
measure, provided each good-annulus event is measurable. -/
theorem measurable_goodAnnulus_radius_count (ρ : ℝ) (hρ : 0 < ρ)
    (n : ℕ) (z : ℂ) (a b : ℝ)
    (hgood : ∀ k : ℕ, MeasurableSet {μ : Measure ℂ |
      IsGoodAnnulus μ (ρ * (7 : ℝ)⁻¹ ^ k) z a b}) :
    Measurable (fun μ : Measure ℂ =>
      ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z a b}.ncard : ℝ)) := by
  let f : ℕ → ℝ := fun k => ρ * (7 : ℝ)⁻¹ ^ k
  have hf : Function.Injective f := by
    intro j k hjk
    have hpow : (7 : ℝ)⁻¹ ^ j = (7 : ℝ)⁻¹ ^ k := by
      exact mul_left_cancel₀ (ne_of_gt hρ) hjk
    exact pow_right_injective₀ (by norm_num : (0 : ℝ) < (7 : ℝ)⁻¹)
      (by norm_num : (7 : ℝ)⁻¹ ≠ 1) hpow
  let S : Measure ℂ → Set ℕ := fun μ => {k |
    f k ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
      1 ≤ k ∧ IsGoodAnnulus μ (f k) z a b}
  have hS : Measurable S := by
    apply measurable_setOfPred.comp
    apply measurable_pi_iff.mpr
    intro k
    apply measurableSet_setOfPred.mp
    by_cases h : f k ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧ 1 ≤ k
    · simp only [h, true_and]
      exact hgood k
    · simp only [← and_assoc, h, false_and]
      exact MeasurableSet.empty
  have hcount : Measurable (fun μ : Measure ℂ => ((S μ).ncard : ℝ)) := by
    exact Measurable.of_discrete.comp (measurable_ncard.comp hS)
  convert hcount using 1
  funext μ
  have heq : {r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
      (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z a b} = f '' S μ := by
    ext r
    constructor
    · rintro ⟨hr, ⟨k, hk, rfl⟩, hg⟩
      exact ⟨k, ⟨hr, hk, hg⟩, rfl⟩
    · rintro ⟨k, ⟨hr, hk, hg⟩, rfl⟩
      exact ⟨hr, ⟨k, hk, rfl⟩, hg⟩
  rw [heq, Set.ncard_image_of_injective _ hf]

/-- The third very-good-annulus condition is measurable if the good-annulus
condition is measurable at each lattice point and geometric radius. -/
theorem measurableSet_veryGoodAnnulus_goodScales (ρ : ℝ) (hρ : 0 < ρ)
    (x₀ : ℂ) (N₀ : ℕ) (a b C₃ : ℝ)
    (hgood : ∀ (n : ℕ) (j k : ℤ) (l : ℕ), MeasurableSet {μ : Measure ℂ |
      IsGoodAnnulus μ (ρ * (7 : ℝ)⁻¹ ^ l)
        (((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)) a b}) :
    MeasurableSet {μ : Measure ℂ |
      ∀ n : ℕ, N₀ ≤ n → ∀ z ∈ annulus x₀ (ρ / 2) ρ,
        (∃ j k : ℤ, z = ((dyadicScale n * ρ / 100 : ℝ) : ℂ) *
          ((j : ℂ) + (k : ℂ) * Complex.I)) →
        C₃ * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
            (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus μ r z a b}.ncard : ℝ)} := by
  let z : ℕ → ℤ → ℤ → ℂ := fun n j k =>
    ((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)
  let T : ℕ → ℤ → ℤ → Set (Measure ℂ) := fun n j k => {μ |
    (N₀ ≤ n ∧ z n j k ∈ annulus x₀ (ρ / 2) ρ) →
      C₃ * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
          (∃ l : ℕ, 1 ≤ l ∧ r = ρ * (7 : ℝ)⁻¹ ^ l) ∧
            IsGoodAnnulus μ r (z n j k) a b}.ncard : ℝ)}
  have hT : ∀ n j k, MeasurableSet (T n j k) := by
    intro n j k
    have hc := measurable_goodAnnulus_radius_count ρ hρ n (z n j k) a b (hgood n j k)
    by_cases h : N₀ ≤ n ∧ z n j k ∈ annulus x₀ (ρ / 2) ρ
    · simpa only [T, h.1, h.2, true_and, true_implies] using measurableSet_le measurable_const hc
    · simp only [T, h, false_implies, ofPred_true, MeasurableSet.univ]
  have heq : {μ : Measure ℂ |
      ∀ n : ℕ, N₀ ≤ n → ∀ w ∈ annulus x₀ (ρ / 2) ρ,
        (∃ j k : ℤ, w = ((dyadicScale n * ρ / 100 : ℝ) : ℂ) *
          ((j : ℂ) + (k : ℂ) * Complex.I)) →
        C₃ * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
            (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus μ r w a b}.ncard : ℝ)} = ⋂ n, ⋂ j, ⋂ k, T n j k := by
    ext μ
    simp only [mem_ofPred_eq, mem_iInter, T]
    constructor
    · intro h n j k ⟨hn, hz⟩
      exact h n hn (z n j k) hz ⟨j, k, rfl⟩
    · intro h n hn w hw hlat
      obtain ⟨j, k, heq⟩ := hlat
      subst w
      exact h n j k ⟨hn, hw⟩
  rw [heq]
  exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun k => hT n j k

/-- Measurability of both size ratios and of the individual good-annulus
events implies measurability of the full very-good-annulus event. -/
theorem measurableSet_isVeryGoodAnnulus_of_measurable_parts
    (βminus ρ : ℝ) (hρ : 0 < ρ) (x₀ : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ)
    (hball : Measurable (fun μ : Measure ℂ =>
      annulusBallMassSize μ βminus ρ x₀ / μ (annulus x₀ (ρ / 4) (2 * ρ))))
    (hgreen : Measurable (fun μ : Measure ℂ =>
      annulusGreenPotentialSup μ x₀ (ρ / 4) (2 * ρ) / μ (annulus x₀ (ρ / 4) (2 * ρ))))
    (hgood : ∀ (n : ℕ) (j k : ℤ) (l : ℕ), MeasurableSet {μ : Measure ℂ |
      IsGoodAnnulus μ (ρ * (7 : ℝ)⁻¹ ^ l)
        (((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)) a b}) :
    MeasurableSet {μ : Measure ℂ |
      IsVeryGoodAnnulus μ βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃} := by
  unfold IsVeryGoodAnnulus
  exact ((isClosed_Icc.measurableSet.preimage hball).inter
    ((isClosed_Icc.measurableSet.preimage hgreen).inter
      (measurableSet_veryGoodAnnulus_goodScales ρ hρ x₀ N₀ a b C₃ hgood)))

end HarmonicBalls
