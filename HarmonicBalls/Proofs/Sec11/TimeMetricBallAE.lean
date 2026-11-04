import HarmonicBalls.Proofs.Sec11.TimeMetricBall
import HarmonicBalls.Steps.Sec11.TimeFamily
import HarmonicBalls.Steps.Sec11.TimeTransferAE

/-! # The time-to-boundary reduction for a harmonic-ball family -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- A locally finite, almost-everywhere exhausting family transfers a typical
boundary-point exclusion to almost every positive time. This does not assume
measurability of the set of exceptional times. -/
theorem ae_time_ne_metricBall_of_ae_entry_cover
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (Λ : ℝ → Set ℂ) (D : ℂ → ℂ → ℝ)
    (z₀ : ℂ) (hfamily : SatisfiesHarmonicBallConditions μ Λ z₀)
    (hcover : ∀ᵐ z ∂μ, ∃ t, 0 < t ∧ z ∈ Λ t)
    (hpoint : ∀ᵐ z ∂μ, ∀ t : ℝ, 0 < t → ∀ w : ℂ, ∀ r : ℝ, 0 < r →
      z ∈ frontier (lqgMetricBall D w r) → Λ t ≠ lqgMetricBall D w r)
    (hnonneg : ∀ w z, 0 ≤ D w z) :
    ∀ᵐ t ∂volume, 0 < t → ∀ w : ℂ, ∀ r : ℝ, Λ t ≠ lqgMetricBall D w r := by
  let τ : ℂ → ℝ := fun z => sInf {t : ℝ | 0 < t ∧ z ∈ Λ t}
  have hopen : ∀ t, 0 < t → IsOpen (Λ t) := fun t ht => (hfamily.isRegularOpen t ht).isOpen
  have hτ : AEMeasurable τ μ := (measurable_positive_entry_time_without_cover Λ hopen).aemeasurable
  have ⟨hmap, hcontfrontier⟩ := hfamily.entry_time_law_and_frontier hcover
  have hcont : ∀ᵐ z ∂μ, ContinuousAt τ z := hcontfrontier.mono fun _ h => h.1
  have hprop : ∀ᵐ z ∂μ, 0 < τ z → ∀ w : ℂ, ∀ r : ℝ, Λ (τ z) ≠ lqgMetricBall D w r := by
    filter_upwards [hcontfrontier, hpoint] with z hz hpointz ht w r heq
    by_cases hr : 0 < r
    · have hb : z ∈ frontier (lqgMetricBall D w r) := by
        rw [← heq]
        exact hz.2 ht
      exact hpointz (τ z) ht w r hr hb heq
    · have hz₀ : z₀ ∈ Λ (τ z) := hfamily.mem (τ z) ht
      have hzballmem : z₀ ∈ lqgMetricBall D w r := heq ▸ hz₀
      have hzball : D w z₀ < r := hzballmem
      exact (not_lt_of_ge (le_trans (le_of_not_gt hr) (hnonneg w z₀))) hzball
  have hp : ∀ᵐ t ∂(μ.map τ), 0 < t → ∀ w : ℂ, ∀ r : ℝ, Λ t ≠ lqgMetricBall D w r :=
    ae_map_of_ae_continuousAt μ τ _ hτ hcont hprop
  rw [hmap] at hp
  have hvol := (ae_restrict_iff' measurableSet_Ioi).1 hp
  filter_upwards [hvol] with t ht hpos
  exact ht hpos hpos

/-- The time-to-boundary reduction without an exhaustion hypothesis: restrict
the measure to the union of the positive-time harmonic balls. -/
theorem ae_time_ne_metricBall_of_ae_boundary_exclusion
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (Λ : ℝ → Set ℂ) (D : ℂ → ℂ → ℝ)
    (z₀ : ℂ) (hfamily : SatisfiesHarmonicBallConditions μ Λ z₀)
    (hpoint : ∀ᵐ z ∂μ, ∀ t : ℝ, 0 < t → ∀ w : ℂ, ∀ r : ℝ, 0 < r →
      z ∈ frontier (lqgMetricBall D w r) → Λ t ≠ lqgMetricBall D w r)
    (hnonneg : ∀ w z, 0 ≤ D w z) :
    ∀ᵐ t ∂volume, 0 < t → ∀ w : ℂ, ∀ r : ℝ, Λ t ≠ lqgMetricBall D w r := by
  let U : Set ℂ := ⋃ t ∈ Ioi (0 : ℝ), Λ t
  have hopen : ∀ t, 0 < t → IsOpen (Λ t) := fun t ht => (hfamily.isRegularOpen t ht).isOpen
  have hU : IsOpen U := isOpen_iUnion fun t => isOpen_iUnion fun ht => hopen t ht
  have hsubset : ∀ t, 0 < t → Λ t ⊆ U := by
    intro t ht x hx
    exact mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨ht, hx⟩⟩
  have hfamily' : SatisfiesHarmonicBallConditions (μ.restrict U) Λ z₀ :=
    { hfamily with
      measure_eq := by
        intro t ht
        rw [Measure.restrict_apply (hopen t ht).measurableSet, inter_eq_left.mpr (hsubset t ht)]
        exact hfamily.measure_eq t ht
      measure_frontier := by
        intro t ht
        apply le_antisymm _ bot_le
        calc
          (μ.restrict U) (frontier (Λ t)) ≤ μ (frontier (Λ t)) := Measure.restrict_apply_le U (frontier (Λ t))
          _ = 0 := hfamily.measure_frontier t ht }
  have hcover : ∀ᵐ z ∂(μ.restrict U), ∃ t, 0 < t ∧ z ∈ Λ t := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    simp only [U, mem_iUnion, mem_Ioi] at hz
    obtain ⟨t, ht, hzt⟩ := hz
    exact ⟨t, ht, hzt⟩
  exact ae_time_ne_metricBall_of_ae_entry_cover (μ.restrict U) Λ D z₀ hfamily' hcover
    (ae_restrict_of_ae hpoint) hnonneg

end HarmonicBalls
