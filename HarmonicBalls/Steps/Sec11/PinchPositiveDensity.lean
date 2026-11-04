import HarmonicBalls.Steps.Sec11.PinchStationaryMean

/-!
# Positive probability and pinch-scale density

This supplies the elementary probability step between the one-scale pinch
event and the fixed-point density conclusion. The positivity, stationarity,
and germ hypotheses remain explicit.
-/

namespace HarmonicBalls

open Set Filter MeasureTheory
open scoped Topology ENNReal

open Classical in
/-- The expectation of a measurable event indicator is its real-valued
probability. -/
theorem integral_event_indicator_eq_measureReal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (E : Set Ω) (hE : MeasurableSet E) :
    (∫ ω, if ω ∈ E then (1 : ℝ) else 0 ∂P) = (P E).toReal := by
  simpa only [Set.indicator_apply, Pi.one_apply, Measure.real] using
    (integral_indicator_one (μ := P) hE)

open Classical in
/-- A positive one-scale probability yields positive block density at a
fixed point under stationarity and the trivial-germ hypotheses. -/
theorem ae_eventually_pinchPointEvent_positive_block_density
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Ω → Measure ℂ)
    (D : Ω → ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M : ℝ) (z : ℂ)
    (X : ℕ → Ω → ℝ)
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
    (hpos : 0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' Q M ((2 : ℝ)⁻¹ ^ 1) z})
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) :
    ∃ δ ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ) := by
  let E : Set Ω := {ω | pinchPointEventWithInternalBounds (μ ω) (D ω)
    U T Q' Q M ((2 : ℝ)⁻¹ ^ 1) z}
  have hEeq : E = X 1 ⁻¹' ({1} : Set ℝ) := by
    ext ω
    simp only [E, mem_ofPred_eq, mem_preimage, mem_singleton_iff, hX]
    split_ifs <;> simp_all
  have hE : MeasurableSet E := by
    rw [hEeq]
    exact (hXm 1) (measurableSet_singleton 1)
  have hq : 0 < (P E).toReal := ENNReal.toReal_pos (ne_of_gt hpos) (measure_ne_top P E)
  have hmean : (∫ ω, X 1 ω ∂P) = (P E).toReal := by
    simp_rw [hX]
    exact integral_event_indicator_eq_measureReal P E hE
  let δ := min ((P E).toReal / 2) (1 / 2)
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδq : δ < ∫ ω, X 1 ω ∂P := by
    rw [hmean]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  exact ⟨δ, ⟨hδ0, hδ1⟩,
    ae_eventually_pinchPointEvent_block_ncard_of_stationary_tail P μ D U T Q' Q M z X δ
      germ hgle hXgerm htrivial hXm hX hBirkhoff hstat hδq hD⟩

end HarmonicBalls
