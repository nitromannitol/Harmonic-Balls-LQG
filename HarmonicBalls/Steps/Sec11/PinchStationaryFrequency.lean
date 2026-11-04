import HarmonicBalls.Steps.Sec11.InternalPinchScales
import HarmonicBalls.Proofs.Sec8.StationaryGoodScales

/-!
# Stationary pinch-scale frequencies

This measure-theoretic step isolates the stationarity, germ measurability,
and positive one-scale probability needed for the pinch argument. It does
not establish these hypotheses for the LQG pinch event.
-/

open Filter MeasureTheory Finset
open scoped Topology BigOperators

namespace HarmonicBalls

/-- Stationary bounded indicators with a trivial scale germ have limiting
frequency equal to their common one-scale expectation. -/
theorem ae_tendsto_initialScaleAverage_of_stationary_trivial_germ
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (q : ℝ)
    (germ : ℝ → MeasurableSpace Ω) (hgle : ∀ ε, 0 < ε → germ ε ≤ mΩ)
    (hXgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      @Measurable Ω ℝ (germ ε) _ (X n))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1)
    (hXm : ∀ n, Measurable (X n))
    (hXbound : ∀ n ω, X n ω ∈ Set.Icc (0 : ℝ) 1)
    (hBirkhoff : PointwiseBirkhoff (P.map (fun ω n => X (n + 1) ω))
      (fun x n => x (n + 1)) (fun x => x 0))
    (hstat : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω))
    (hmean : ∀ n, ∫ ω, X n ω ∂P = q) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ))
      atTop (𝓝 q) := by
  have hXi : ∀ n, Integrable (X n) P := by
    intro n
    apply Integrable.mono' (integrable_const (1 : ℝ)) (hXm n).aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hXbound n ω).1]
    exact (hXbound n ω).2
  have hlim := ae_tendsto_initialScaleAverage_of_stationary P X hBirkhoff hXm (hXi 1) hstat
  let L : Ω → ℝ := fun ω => limUnder atTop
    (fun N : ℕ => (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ))
  have hLm : ∀ ε, 0 < ε → @Measurable Ω ℝ (germ ε) _ L :=
    germ_measurable_initialScaleFrequency germ X hXgerm
  obtain ⟨c, hc⟩ := ae_eq_const_of_trivial_germ P germ hgle L hLm htrivial
  have hlimc : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ)) atTop (𝓝 c) := by
    filter_upwards [hlim, hc] with ω hω hωc
    have h := tendsto_nhds_limUnder hω
    change Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ))
      atTop (𝓝 (L ω)) at h
    simpa only [hωc] using h
  have hcq : c = q := by
    apply constant_limit_eq_of_eventually_integral_eq P
      (fun N ω => (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ)) c q 1
    · intro N
      exact (integrable_initialScaleAverage P X hXi N).aestronglyMeasurable
    · intro N
      filter_upwards with ω
      have h := initialScaleAverage_mem_Icc (fun n => X n ω) (fun n => hXbound n ω) N
      rw [Real.norm_eq_abs, abs_of_nonneg h.1]
      exact h.2
    · exact hlimc
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
      exact integral_initialScaleAverage_eq P X q hXi hmean (by omega)
  simpa only [hcq] using hlimc

open Classical in
/-- The stationary and trivial-germ hypotheses give positive pinch-scale
block density at a fixed point, provided the one-scale expectation is positive. -/
theorem ae_eventually_pinchPointEvent_block_ncard_of_stationary
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Ω → Measure ℂ)
    (D : Ω → ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M : ℝ) (z : ℂ)
    (X : ℕ → Ω → ℝ) (q δ : ℝ)
    (germ : ℝ → MeasurableSpace Ω) (hgle : ∀ ε, 0 < ε → germ ε ≤ mΩ)
    (hXgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      @Measurable Ω ℝ (germ ε) _ (X n))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1)
    (hXm : ∀ n, Measurable (X n))
    (hX : ∀ n ω, X n ω = if pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z then 1 else 0)
    (hBirkhoff : PointwiseBirkhoff (P.map (fun ω n => X (n + 1) ω))
      (fun x n => x (n + 1)) (fun x => x 0))
    (hstat : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω))
    (hmean : ∀ n, ∫ ω, X n ω ∂P = q) (hδ : δ < q)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ) := by
  have hbound : ∀ n ω, X n ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro n ω
    rw [hX]
    split_ifs <;> norm_num
  have hlim := ae_tendsto_initialScaleAverage_of_stationary_trivial_germ P X q germ
    hgle hXgerm htrivial hXm hbound hBirkhoff hstat hmean
  filter_upwards [hlim, hD] with ω hω hDω
  apply eventually_pinchPointEvent_block_ncard_of_internalFrequency hDω hδ
  simpa only [hX] using hω

end HarmonicBalls
