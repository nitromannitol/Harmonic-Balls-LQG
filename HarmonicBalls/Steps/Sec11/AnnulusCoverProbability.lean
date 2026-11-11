import HarmonicBalls.Steps.Sec11.FiniteAnnulusCoverChains
import HarmonicBalls.Steps.Sec11.AnnulusNormalizedDecay

/-! # Annular exceedances from local cover estimates

A fixed number of overlapping pieces transfers summable local exceedance
bounds to the annular corridor. No measurability of the exceedance events is
needed, and the length-metric property need only hold almost everywhere.
-/

namespace HarmonicBalls

open Set MeasureTheory
open scoped ENNReal

/-- The finite-chain union bound remains valid when the metric property holds
only almost everywhere. -/
theorem measure_internalMetric_cover_chain_exceedance_le_of_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → ℂ → ℂ → ℝ) (U K : Set ℂ)
    (A W : ℕ → Set ℂ) (z : ℕ → ℂ) (N : ℕ) (C : Ω → ℝ≥0∞)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hz : ∀ i < N, z (i + 1) ∈ A i ∧ z (i + 1) ∈ A (i + 1))
    (hcover : ∀ x ∈ K, ∃ i ≤ N, x ∈ A i)
    (hWU : ∀ i ≤ N, W i ⊆ U) :
    P {ω | ∃ x ∈ K, ∃ y ∈ K, (N + 1 : ℕ) * C ω < internalMetric (D ω) U x y} ≤
      ∑ i ∈ Finset.range (N + 1), P {ω | ∃ x ∈ A i, ∃ y ∈ A i,
        C ω < internalMetric (D ω) (W i) x y} := by
  have hnull : P {ω | ¬ IsEuclideanLengthMetric (D ω)} = 0 := by
    simpa only [ae_iff] using hmetric
  calc
    _ ≤ P ({ω | IsEuclideanLengthMetric (D ω) ∧
        ∃ x ∈ K, ∃ y ∈ K, (N + 1 : ℕ) * C ω < internalMetric (D ω) U x y} ∪
        {ω | ¬ IsEuclideanLengthMetric (D ω)}) := by
      apply measure_mono
      intro ω hω
      by_cases h : IsEuclideanLengthMetric (D ω)
      · exact Or.inl ⟨h, hω⟩
      · exact Or.inr h
    _ ≤ P {ω | IsEuclideanLengthMetric (D ω) ∧
        ∃ x ∈ K, ∃ y ∈ K, (N + 1 : ℕ) * C ω < internalMetric (D ω) U x y} +
        P {ω | ¬ IsEuclideanLengthMetric (D ω)} := measure_union_le _ _
    _ ≤ _ := by
      rw [hnull, add_zero]
      exact measure_internalMetric_cover_chain_exceedance_le P D U K A W z N C hz hcover hWU

/-- Uniform summable local exceedance estimates imply the normalized annular
summability condition, allowing the pieces and their centers to vary by scale. -/
theorem summable_annulus_exceedance_of_finite_cover_chains
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → ℂ → ℂ → ℝ) (A : Ω → ℝ≥0∞) (s β : ℝ) (N : ℕ)
    (pieces domains : ℕ → ℕ → Set ℂ) (z : ℕ → ℕ → ℂ) (p : ℕ → ℝ≥0∞)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hz : ∀ n i, i < N → z n (i + 1) ∈ pieces n i ∧ z n (i + 1) ∈ pieces n (i + 1))
    (hcover : ∀ n x, x ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n →
      ∃ i ≤ N, x ∈ pieces n i)
    (hWU : ∀ n i, i ≤ N → domains n i ⊆ exponentialAnnulusCorridor s n)
    (hlocal : ∀ n i, i ≤ N →
      P {ω | ∃ x ∈ pieces n i, ∃ y ∈ pieces n i,
        A ω * ENNReal.ofReal (Real.exp (-β * (n : ℝ))) <
          internalMetric (D ω) (domains n i) x y} ≤ p n)
    (hp : (∑' n, p n) ≠ ∞) :
    (∑' n, P {ω | ∃ x ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
      ∃ y ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
        ((N + 1 : ℕ) * A ω) * ENNReal.ofReal (Real.exp (-β * (n : ℝ))) <
          internalMetric (D ω) (exponentialAnnulusCorridor s n) x y}) ≠ ∞ := by
  apply ne_of_lt
  calc
    _ ≤ ∑' n, ((N + 1 : ℕ) : ℝ≥0∞) * p n := by
      apply ENNReal.tsum_le_tsum
      intro n
      calc
        _ ≤ ∑ i ∈ Finset.range (N + 1), P {ω | ∃ x ∈ pieces n i, ∃ y ∈ pieces n i,
            A ω * ENNReal.ofReal (Real.exp (-β * (n : ℝ))) <
              internalMetric (D ω) (domains n i) x y} := by
          simpa only [mul_assoc] using
            measure_internalMetric_cover_chain_exceedance_le_of_ae P D
              (exponentialAnnulusCorridor s n)
              (geometricShell (Real.exp (-s)) (Real.exp (-1)) n)
              (pieces n) (domains n) (z n) N
              (fun ω => A ω * ENNReal.ofReal (Real.exp (-β * (n : ℝ))))
              hmetric (hz n) (hcover n) (hWU n)
        _ ≤ ∑ _i ∈ Finset.range (N + 1), p n := by
          apply Finset.sum_le_sum
          intro i hi
          exact hlocal n i (by have := Finset.mem_range.mp hi; omega)
        _ = ((N + 1 : ℕ) : ℝ≥0∞) * p n := by simp
    _ = ((N + 1 : ℕ) : ℝ≥0∞) * ∑' n, p n := ENNReal.tsum_mul_left
    _ < ∞ := ENNReal.mul_lt_top (by simp) (lt_top_iff_ne_top.mpr hp)


/-- Summable local cover estimates imply removal of the origin for the
logarithmically Weyl-scaled metric, under the explicit metric and Weyl
assumptions. -/
theorem ae_internalMetric_sdiff_zero_eq_of_local_cover_exceedance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D E : Ω → ℂ → ℂ → ℝ) (A : Ω → ℝ≥0∞) (s ξ α β : ℝ) (N : ℕ)
    (pieces domains : ℕ → ℕ → Set ℂ) (z : ℕ → ℕ → ℂ) (p : ℕ → ℝ≥0∞)
    (hξ : 0 ≤ ξ) (hα : 0 ≤ α) (hgap : ξ * α < β)
    (V : Set ℂ) (hball : Metric.ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hDnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y)
    (hEnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ E ω x y)
    (hA : ∀ᵐ ω ∂P, A ω ≠ ∞)
    (hzero : ∀ᵐ ω ∂P, ∀ x y,
      weylScaling (D ω) ξ 0 x y = ENNReal.ofReal (D ω x y))
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (D ω) ξ (fun z => -α * Real.log ‖z‖) x y)
    (hz : ∀ n i, i < N → z n (i + 1) ∈ pieces n i ∧ z n (i + 1) ∈ pieces n (i + 1))
    (hcover : ∀ n x, x ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n →
      ∃ i ≤ N, x ∈ pieces n i)
    (hWU : ∀ n i, i ≤ N → domains n i ⊆ exponentialAnnulusCorridor s n)
    (hlocal : ∀ n i, i ≤ N →
      P {ω | ∃ x ∈ pieces n i, ∃ y ∈ pieces n i,
        A ω * ENNReal.ofReal (Real.exp (-β * (n : ℝ))) <
          internalMetric (D ω) (domains n i) x y} ≤ p n)
    (hp : (∑' n, p n) ≠ ∞) :
    ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
      internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y := by
  have hA' : ∀ᵐ ω ∂P, ((N + 1 : ℕ) : ℝ≥0∞) * A ω ≠ ∞ := by
    filter_upwards [hA] with ω hω
    exact ENNReal.mul_ne_top (by simp) hω
  exact ae_internalMetric_sdiff_zero_eq_of_normalized_annulus_exceedance P D E
    (fun ω => ((N + 1 : ℕ) : ℝ≥0∞) * A ω) s ξ α β hξ hα hgap V hball
    hD hE hDnonneg hEnonneg hA' hzero hscale
    (summable_annulus_exceedance_of_finite_cover_chains P D A s β N pieces domains z p
      hD hz hcover hWU hlocal hp)


end HarmonicBalls
