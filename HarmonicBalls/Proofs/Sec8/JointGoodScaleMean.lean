import HarmonicBalls.Proofs.Sec8.JointGoodScaleProbability
import HarmonicBalls.Proofs.Sec8.StationaryMoments

/-! # From one-scale failure probability to frequency -/

open MeasureTheory Filter Finset ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

open Classical in
/-- A measurable indicator has expectation greater than `1 - ζ` whenever
its failure probability is bounded by a smaller nonnegative number. -/
theorem integral_indicator_gt_of_failure_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (X : Ω → ℝ) (hXm : Measurable X)
    (hX : ∀ ω, X ω = if ω ∈ A then 1 else 0)
    {ε ζ : ℝ} (hε : 0 ≤ ε) (hεζ : ε < ζ)
    (hfail : P Aᶜ ≤ ENNReal.ofReal ε) :
    1 - ζ < ∫ ω, X ω ∂P := by
  have hAeq : A = X ⁻¹' {1} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hX]
    split_ifs <;> simp_all
  have hA : MeasurableSet A := by
    rw [hAeq]
    exact hXm (measurableSet_singleton 1)
  have hsum : P.real A + P.real Aᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hA, probReal_univ]
  have hbound : P.real Aᶜ ≤ ε := by
    change (P Aᶜ).toReal ≤ ε
    have ht := (ENNReal.toReal_le_toReal (measure_ne_top P Aᶜ) ENNReal.ofReal_ne_top).2 hfail
    simpa [ENNReal.toReal_ofReal hε] using ht
  rw [integral_eq_measure_of_indicator P A X hXm hX]
  change 1 - ζ < P.real A
  linarith

open Classical in
/-- The stationary block-frequency conclusion follows from a one-scale
failure estimate and the explicit germ, stationarity and ergodic hypotheses. -/
theorem ae_eventually_veryGoodComparableScaleCount_of_stationary_and_small_failure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (X : ℕ → Ω → ℝ) (ζ ε : ℝ)
    (germ : ℝ → MeasurableSpace Ω) (hgle : ∀ r, 0 < r → germ r ≤ mΩ)
    (hXgerm : ∀ r, 0 < r → ∃ K, ∀ n, K ≤ n →
      @Measurable Ω ℝ (germ r) _ (X n))
    (htrivial : ∀ A : Set Ω, (∀ r, 0 < r → MeasurableSet[germ r] A) →
      P A = 0 ∨ P A = 1)
    (hX : ∀ n ω, X n ω = if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) z N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n z m then 1 else 0)
    (hXm : ∀ n, Measurable (X n))
    (hBirkhoff : PointwiseBirkhoff (P.map (fun ω n => X (n + 1) ω))
      (fun x n => x (n + 1)) (fun x => x 0))
    (hstat : P.map (fun ω n => X (n + 1) ω) = P.map (fun ω n => X n ω))
    (hε : 0 ≤ ε) (hεζ : ε < ζ)
    (hfail : P {ω | ¬ (IsVeryGoodAnnulus (μ ω) βminus (dyadicScale 0) z N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) 0 z m)} ≤ ENNReal.ofReal ε) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      veryGoodComparableScaleCount (μ ω) βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N := by
  let A : Set Ω := {ω | IsVeryGoodAnnulus (μ ω) βminus (dyadicScale 0) z N₀
    a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) 0 z m}
  have hmean : 1 - ζ < ∫ ω, X 0 ω ∂P :=
    integral_indicator_gt_of_failure_le P A (X 0) (hXm 0) (by
        intro ω
        rw [hX]
        by_cases hω : IsVeryGoodAnnulus (μ ω) βminus (dyadicScale 0) z N₀
            a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) 0 z m
        · simp only [A, Set.mem_ofPred_eq, hω]
        · simp only [A, Set.mem_ofPred_eq, hω, ↓reduceIte])
      hε hεζ hfail
  exact ae_eventually_veryGoodComparableScaleCount_of_stationary_first_mean P μ βminus z N₀
    a b C₁m C₁p C₂m C₂p C₃ m X ζ germ hgle hXgerm htrivial hX hXm hBirkhoff hstat hmean

end HarmonicBalls
