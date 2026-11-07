import HarmonicBalls.Proofs.Sec8.GermLimit
import HarmonicBalls.Proofs.Sec8.StationaryBirkhoff

/-!
# Stationary good-scale frequencies

Birkhoff convergence and germ triviality give the block-frequency estimate
once the indicator process has the stated stationarity and locality properties.
-/

open Filter MeasureTheory Finset
open scoped Topology BigOperators

namespace HarmonicBalls

/-- Initial averages over indices `1, ..., N` converge for a stationary tail. -/
theorem ae_tendsto_initialScaleAverage_of_stationary {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (_hBirkhoff : PointwiseBirkhoff (P.map (fun ω n => X (n + 1) ω))
      (fun x n => x (n + 1)) (fun x => x 0))
    (hXm : ∀ n, Measurable (X n)) (hInt : Integrable (X 1) P)
    (hstat : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω)) :
    ∀ᵐ ω ∂P, ∃ c : ℝ, Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ)) atTop (𝓝 c) := by
  have hstat' : P.map (fun ω n => X ((n + 1) + 1) ω) =
      P.map (fun ω n => X (n + 1) ω) := by simpa [Nat.add_assoc] using hstat
  have h := ae_tendsto_stationary_average P (fun n => X (n + 1))
    (fun n => hXm (n + 1)) hInt hstat'
  filter_upwards [h] with ω ⟨c, hc⟩
  refine ⟨c, ?_⟩
  convert hc using 1
  funext N
  have hsum : (∑ n ∈ Icc 1 N, X n ω) = ∑ n ∈ range N, X (n + 1) ω := by
    symm
    apply Finset.sum_bij (fun n _ => n + 1)
    · intro n hn
      simp only [mem_range] at hn
      simp only [mem_Icc]
      omega
    · intro a ha b hb hab
      omega
    · intro b hb
      simp only [mem_Icc] at hb
      refine ⟨b - 1, ?_, ?_⟩
      · simp only [mem_range]; omega
      · omega
    · intro a ha
      rfl
  rw [hsum, div_eq_mul_inv, mul_comm]

open Classical in
/-- A stationary sequence of good-scale indicators has the desired block
frequency when its limiting frequency is measurable in a trivial germ. -/
theorem ae_eventually_veryGoodComparableScaleCount_of_stationary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (X : ℕ → Ω → ℝ) (q ζ : ℝ)
    (germ : ℝ → MeasurableSpace Ω) (hgle : ∀ ε, 0 < ε → germ ε ≤ mΩ)
    (hXgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      @Measurable Ω ℝ (germ ε) _ (X n))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1)
    (hX : ∀ n ω, X n ω = if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) z N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n z m then 1 else 0)
    (hXm : ∀ n, Measurable (X n))
    (hBirkhoff : PointwiseBirkhoff (P.map (fun ω n => X (n + 1) ω))
      (fun x n => x (n + 1)) (fun x => x 0))
    (hstat : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω))
    (hmean : ∀ n, ∫ ω, X n ω ∂P = q) (hq : 1 - ζ < q) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      veryGoodComparableScaleCount (μ ω) βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N := by
  have hInt : Integrable (X 1) P := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (hXm 1).aestronglyMeasurable
    filter_upwards with ω
    rw [hX]
    split_ifs <;> norm_num
  have hlim := ae_tendsto_initialScaleAverage_of_stationary P X hBirkhoff hXm hInt hstat
  exact ae_eventually_veryGoodComparableScaleCount_of_convergence P μ βminus z N₀
    a b C₁m C₁p C₂m C₂p C₃ m X q ζ germ hgle hXgerm htrivial hX hXm hlim hmean hq

end HarmonicBalls
