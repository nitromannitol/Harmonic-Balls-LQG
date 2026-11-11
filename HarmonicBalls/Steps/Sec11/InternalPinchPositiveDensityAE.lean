import HarmonicBalls.Steps.Sec11.PinchPositiveDensity

/-! # Internal pinch-scale density from almost-sure event representatives -/

namespace HarmonicBalls

open Set Filter MeasureTheory
open scoped Topology ENNReal

open Classical in
/-- Positive probability gives fixed-point density of pinch scales with internal bounds when the
bounded stationary process represents the event only almost surely. -/
theorem ae_eventually_internal_pinch_positive_block_density_of_ae_rep
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Ω → Measure ℂ)
    (D : Ω → ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M : ℝ) (z : ℂ)
    (X : ℕ → Ω → ℝ)
    (germ : ℝ → MeasurableSpace Ω) (hgle : ∀ ε, 0 < ε → germ ε ≤ mΩ)
    (hXgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      @Measurable Ω ℝ (germ ε) _ (X n))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1)
    (hXm : ∀ n, Measurable (X n)) (hbound : ∀ n ω, X n ω ∈ Icc (0 : ℝ) 1)
    (hX : ∀ᵐ ω ∂P, ∀ n, X n ω = if pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z then 1 else 0)
    (hBirkhoff : PointwiseBirkhoff (P.map (fun ω n => X (n + 1) ω))
      (fun x n => x (n + 1)) (fun x => x 0))
    (hstat : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω))
    (hpos : 0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' Q M ((2 : ℝ)⁻¹ ^ 1) z}) :
    ∃ δ ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ) := by
  let E : Set Ω := {ω | pinchPointEventWithInternalBounds (μ ω) (D ω)
    U T Q' Q M ((2 : ℝ)⁻¹ ^ 1) z}
  let E' : Set Ω := X 1 ⁻¹' ({1} : Set ℝ)
  have hE' : MeasurableSet E' := (hXm 1) (measurableSet_singleton 1)
  have hEq : E =ᵐ[P] E' := by
    filter_upwards [hX] with ω hω
    simp only [E, E', mem_ofPred_eq, mem_preimage, mem_singleton_iff, hω 1]
    split_ifs <;> simp_all
  have hmeasure : P E = P E' := measure_congr hEq
  have hq : 0 < (P E').toReal := ENNReal.toReal_pos (by rw [← hmeasure]; exact ne_of_gt hpos)
    (measure_ne_top P E')
  have hmean : (∫ ω, X 1 ω ∂P) = (P E').toReal := by
    rw [← integral_event_indicator_eq_measureReal P E' hE']
    apply integral_congr_ae
    filter_upwards [hX] with ω hω
    simp only [E', mem_preimage, mem_singleton_iff, hω 1]
    split_ifs <;> simp_all
  let δ := min ((P E').toReal / 2) (1 / 2)
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδq : δ < ∫ ω, X 1 ω ∂P := by
    rw [hmean]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hlim := ae_tendsto_initialScaleAverage_of_stationary_tail_trivial_germ P X germ
    hgle hXgerm htrivial hXm hbound hBirkhoff hstat
  refine ⟨δ, ⟨hδ0, hδ1⟩, ?_⟩
  filter_upwards [hlim, hX] with ω hlim hXω
  have hlim' : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N,
        if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
          ((2 : ℝ)⁻¹ ^ n) z then (1 : ℝ) else 0) / (N : ℝ))
      atTop (𝓝 (∫ ω, X 1 ω ∂P)) := by
    simpa only [hXω] using hlim
  have hf := eventually_goodScale_block_ncard
    (fun n => pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
      ((2 : ℝ)⁻¹ ^ n) z) hlim' hδq
  filter_upwards [hf] with N hN
  simpa only [Set.mem_Icc, and_assoc] using hN


end HarmonicBalls
