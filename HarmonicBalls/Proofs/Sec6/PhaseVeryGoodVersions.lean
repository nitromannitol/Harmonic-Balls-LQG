import HarmonicBalls.Proofs.Sec6.PhaseVeryGoodSizeLocality
import HarmonicBalls.Proofs.Sec8.VeryGoodMeasureVersion

/-! # Measurable versions for fixed phase

The imported locality development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization of the ergodic theorem.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls.Section6

open Classical in
/-- Countable measurable versions of individual good-annulus events give a
measurable version of the lattice good-scale condition. -/
theorem exists_measurable_phaseVeryGood_goodScales_version
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (x₀ phase : ℂ) (N₀ : ℕ) (a b C₃ : ℝ)
    (hgood : ∀ (n : ℕ) (j k : ℤ) (l : ℕ), ∃ A : Set Ω, MeasurableSet A ∧ ∀ᵐ ω ∂P,
      (ω ∈ A ↔ IsGoodAnnulus (μ ω) (ρ * (7 : ℝ)⁻¹ ^ l)
        (phase + ((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)) a b)) :
    ∃ A : Set Ω, MeasurableSet A ∧ ∀ᵐ ω ∂P,
      (ω ∈ A ↔ ∀ n : ℕ, N₀ ≤ n → ∀ z ∈ annulus x₀ (ρ / 2) ρ,
        z - phase ∈ Section6.scaledLattice (dyadicScale n * ρ / 100) →
        C₃ * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
            (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)) := by
  let z : ℕ → ℤ → ℤ → ℂ := fun n j k =>
    phase + ((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)
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
    change ∃ j k : ℤ, w - phase = _ at hlat
    obtain ⟨j, k, heq⟩ := hlat
    have hw_eq : w = z n j k := by dsimp [z]; linear_combination heq
    subst w
    simpa only [hω n j k] using h n j k ⟨hn, hw⟩
  · intro h n j k ⟨hn, hz⟩
    rw [hω n j k]
    apply h n hn (z n j k) hz
    apply Section6.mem_scaledLattice.mpr
    exact ⟨j, k, by simp [z]⟩

open Classical in
/-- The very-good-annulus event has a measurable version when its two size
ratios and each good-annulus event have measurable versions. -/
theorem exists_measurable_phaseVeryGoodAnnulus_version
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (βminus ρ : ℝ) (hρ : 0 < ρ) (x₀ phase : ℂ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ)
    (hball : AEMeasurable (fun ω => annulusBallMassSize (μ ω) βminus ρ x₀ /
      μ ω (annulus x₀ (ρ / 4) (2 * ρ))) P)
    (hgreen : AEMeasurable (fun ω => annulusGreenPotentialSup (μ ω) x₀ (ρ / 4) (2 * ρ) /
      μ ω (annulus x₀ (ρ / 4) (2 * ρ))) P)
    (hgood : ∀ (n : ℕ) (j k : ℤ) (l : ℕ), ∃ A : Set Ω, MeasurableSet A ∧ ∀ᵐ ω ∂P,
      (ω ∈ A ↔ IsGoodAnnulus (μ ω) (ρ * (7 : ℝ)⁻¹ ^ l)
        (phase + ((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)) a b)) :
    ∃ A : Set Ω, MeasurableSet A ∧ ∀ᵐ ω ∂P,
      (ω ∈ A ↔ PhaseVeryGoodAnnulus (μ ω) βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ phase) := by
  obtain ⟨G, hG, hGrep⟩ := exists_measurable_phaseVeryGood_goodScales_version
    P μ ρ hρ x₀ phase N₀ a b C₃ hgood
  let F : Ω → ℝ≥0∞ := fun ω => annulusBallMassSize (μ ω) βminus ρ x₀ /
    μ ω (annulus x₀ (ρ / 4) (2 * ρ))
  let H : Ω → ℝ≥0∞ := fun ω => annulusGreenPotentialSup (μ ω) x₀ (ρ / 4) (2 * ρ) /
    μ ω (annulus x₀ (ρ / 4) (2 * ρ))
  refine ⟨(hball.mk F ⁻¹' Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)) ∩
    (hgreen.mk H ⁻¹' Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)) ∩ G, ?_, ?_⟩
  · exact ((isClosed_Icc.measurableSet.preimage hball.measurable_mk).inter
      (isClosed_Icc.measurableSet.preimage hgreen.measurable_mk)).inter hG
  · filter_upwards [hball.ae_eq_mk, hgreen.ae_eq_mk, hGrep] with ω hF hH hω
    simp only [mem_inter_iff, mem_preimage, ← hF, ← hH, hω, PhaseVeryGoodAnnulus, PhaseVeryGoodCriterionThree, F, H,
      and_assoc]

end HarmonicBalls.Section6
