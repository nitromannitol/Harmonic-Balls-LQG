import HarmonicBalls.Proofs.Sec8.VeryGoodCountMeasurable

/-! # Measurable versions of good-radius counts -/

open MeasureTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

open Classical in
/-- Countably many almost-sure measurable versions of good-annulus events give
an almost-sure measurable version of the good-radius count. -/
theorem exists_measurable_goodAnnulus_radius_count_version
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (z : ℂ) (a b : ℝ)
    (hgood : ∀ k : ℕ, ∃ A : Set Ω, MeasurableSet A ∧ ∀ᵐ ω ∂P,
      (ω ∈ A ↔ IsGoodAnnulus (μ ω) (ρ * (7 : ℝ)⁻¹ ^ k) z a b)) :
    ∃ Y : Ω → ℝ, Measurable Y ∧ ∀ᵐ ω ∂P,
      Y ω = ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
        IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ) := by
  choose A hA hrep using hgood
  let f : ℕ → ℝ := fun k => ρ * (7 : ℝ)⁻¹ ^ k
  have hf : Function.Injective f := by
    intro j k hjk
    have hpow : (7 : ℝ)⁻¹ ^ j = (7 : ℝ)⁻¹ ^ k := mul_left_cancel₀ (ne_of_gt hρ) hjk
    exact pow_right_injective₀ (by norm_num : (0 : ℝ) < (7 : ℝ)⁻¹)
      (by norm_num : (7 : ℝ)⁻¹ ≠ 1) hpow
  let S : Ω → Set ℕ := fun ω => {k |
    f k ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
      1 ≤ k ∧ ω ∈ A k}
  have hS : Measurable S := by
    apply measurable_setOfPred.comp
    apply measurable_pi_iff.mpr
    intro k
    apply measurableSet_setOfPred.mp
    by_cases h : f k ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧ 1 ≤ k
    · simpa only [h, true_and, ofPred_mem_eq] using hA k
    · simp only [← and_assoc, h, false_and, ofPred_false, MeasurableSet.empty]
  refine ⟨fun ω => ((S ω).ncard : ℝ), Measurable.of_discrete.comp (measurable_ncard.comp hS), ?_⟩
  filter_upwards [ae_all_iff.mpr hrep] with ω hω
  have heq : {r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
      (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
      IsGoodAnnulus (μ ω) r z a b} = f '' S ω := by
    ext r
    constructor
    · rintro ⟨hr, ⟨k, hk, rfl⟩, hg⟩
      exact ⟨k, ⟨hr, hk, (hω k).mpr hg⟩, rfl⟩
    · rintro ⟨k, ⟨hr, hk, hg⟩, rfl⟩
      exact ⟨hr, ⟨k, hk, rfl⟩, (hω k).mp hg⟩
  rw [heq, Set.ncard_image_of_injective _ hf]

open Classical in
/-- Countable measurable versions of individual good-annulus events give a
measurable version of the lattice good-scale condition. -/
theorem exists_measurable_veryGoodAnnulus_goodScales_version
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (x₀ : ℂ) (N₀ : ℕ) (a b C₃ : ℝ)
    (hgood : ∀ (n : ℕ) (j k : ℤ) (l : ℕ), ∃ A : Set Ω, MeasurableSet A ∧ ∀ᵐ ω ∂P,
      (ω ∈ A ↔ IsGoodAnnulus (μ ω) (ρ * (7 : ℝ)⁻¹ ^ l)
        (((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)) a b)) :
    ∃ A : Set Ω, MeasurableSet A ∧ ∀ᵐ ω ∂P,
      (ω ∈ A ↔ ∀ n : ℕ, N₀ ≤ n → ∀ z ∈ annulus x₀ (ρ / 2) ρ,
        (∃ j k : ℤ, z = ((dyadicScale n * ρ / 100 : ℝ) : ℂ) *
          ((j : ℂ) + (k : ℂ) * Complex.I)) →
        C₃ * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
            (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)) := by
  let z : ℕ → ℤ → ℤ → ℂ := fun n j k =>
    ((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)
  have hex : ∀ (n : ℕ) (j k : ℤ), ∃ Y : Ω → ℝ, Measurable Y ∧ ∀ᵐ ω ∂P,
      Y ω = ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ l : ℕ, 1 ≤ l ∧ r = ρ * (7 : ℝ)⁻¹ ^ l) ∧
          IsGoodAnnulus (μ ω) r (z n j k) a b}.ncard : ℝ) := by
    intro n j k
    exact exists_measurable_goodAnnulus_radius_count_version P μ ρ hρ n (z n j k) a b (hgood n j k)
  choose Y hY hrep using hex
  let T : ℕ → ℤ → ℤ → Set Ω := fun n j k => {ω |
    (N₀ ≤ n ∧ z n j k ∈ annulus x₀ (ρ / 2) ρ) →
      C₃ * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤ Y n j k ω}
  have hT : ∀ n j k, MeasurableSet (T n j k) := by
    intro n j k
    by_cases h : N₀ ≤ n ∧ z n j k ∈ annulus x₀ (ρ / 2) ρ
    · simpa only [T, h.1, h.2, true_and, true_implies] using measurableSet_le measurable_const (hY n j k)
    · simp only [T, h, false_implies, ofPred_true, MeasurableSet.univ]
  refine ⟨⋂ n, ⋂ j, ⋂ k, T n j k,
    MeasurableSet.iInter fun n => MeasurableSet.iInter fun j => MeasurableSet.iInter fun k => hT n j k, ?_⟩
  filter_upwards [ae_all_iff.mpr fun n => ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => hrep n j k] with ω hω
  simp only [mem_iInter, T, mem_ofPred_eq]
  constructor
  · intro h n hn w hw hlat
    obtain ⟨j, k, heq⟩ := hlat
    subst w
    simpa only [hω n j k] using h n j k ⟨hn, hw⟩
  · intro h n j k ⟨hn, hz⟩
    rw [hω n j k]
    exact h n hn (z n j k) hz ⟨j, k, rfl⟩

open Classical in
/-- The very-good-annulus event has a measurable version when its two size
ratios and each good-annulus event have measurable versions. -/
theorem exists_measurable_isVeryGoodAnnulus_version
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (βminus ρ : ℝ) (hρ : 0 < ρ) (x₀ : ℂ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ)
    (hball : AEMeasurable (fun ω => annulusBallMassSize (μ ω) βminus ρ x₀ /
      μ ω (annulus x₀ (ρ / 4) (2 * ρ))) P)
    (hgreen : AEMeasurable (fun ω => annulusGreenPotentialSup (μ ω) x₀ (ρ / 4) (2 * ρ) /
      μ ω (annulus x₀ (ρ / 4) (2 * ρ))) P)
    (hgood : ∀ (n : ℕ) (j k : ℤ) (l : ℕ), ∃ A : Set Ω, MeasurableSet A ∧ ∀ᵐ ω ∂P,
      (ω ∈ A ↔ IsGoodAnnulus (μ ω) (ρ * (7 : ℝ)⁻¹ ^ l)
        (((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)) a b)) :
    ∃ A : Set Ω, MeasurableSet A ∧ ∀ᵐ ω ∂P,
      (ω ∈ A ↔ IsVeryGoodAnnulus (μ ω) βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃) := by
  obtain ⟨G, hG, hGrep⟩ := exists_measurable_veryGoodAnnulus_goodScales_version
    P μ ρ hρ x₀ N₀ a b C₃ hgood
  let F : Ω → ℝ≥0∞ := fun ω => annulusBallMassSize (μ ω) βminus ρ x₀ /
    μ ω (annulus x₀ (ρ / 4) (2 * ρ))
  let H : Ω → ℝ≥0∞ := fun ω => annulusGreenPotentialSup (μ ω) x₀ (ρ / 4) (2 * ρ) /
    μ ω (annulus x₀ (ρ / 4) (2 * ρ))
  refine ⟨(hball.mk F ⁻¹' Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)) ∩
    (hgreen.mk H ⁻¹' Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)) ∩ G, ?_, ?_⟩
  · exact ((isClosed_Icc.measurableSet.preimage hball.measurable_mk).inter
      (isClosed_Icc.measurableSet.preimage hgreen.measurable_mk)).inter hG
  · filter_upwards [hball.ae_eq_mk, hgreen.ae_eq_mk, hGrep] with ω hF hH hω
    simp only [mem_inter_iff, mem_preimage, ← hF, ← hH, hω, IsVeryGoodAnnulus, F, H,
      and_assoc]

end HarmonicBalls
