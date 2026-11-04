import HarmonicBalls.Proofs.Sec11.TypicalBoundary
import HarmonicBalls.Steps.Sec11.TimeTransfer

/-! # Transferring the metric-ball exclusion to time -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- A countable compact cover of typical boundary points transfers the
pointwise metric-ball exclusion to almost every positive time, even if the
set of exceptional times is not known to be measurable. The construction of
the cover and the entry-time distribution are separate steps. -/
theorem ae_time_ne_metricBall_of_compact_entry_cover
    (μ : Measure ℂ) (Λ : ℝ → Set ℂ) (D : ℂ → ℂ → ℝ)
    (τ : ℂ → ℝ) (K : ℕ → Set ℂ)
    (hτ : AEMeasurable τ μ) (hmap : μ.map τ = volume.restrict (Ioi (0 : ℝ)))
    (hcompact : ∀ n, IsCompact (K n)) (hcont : ∀ n, ContinuousOn τ (K n))
    (hfull : ∀ᵐ z ∂μ, z ∈ ⋃ n, K n)
    (hboundary : ∀ n z, z ∈ K n → 0 < τ z → z ∈ frontier (Λ (τ z)))
    (hpoint : ∀ n z, z ∈ K n → ∀ t : ℝ, 0 < t → ∀ w : ℂ, ∀ r : ℝ, 0 < r →
      z ∈ frontier (lqgMetricBall D w r) → Λ t ≠ lqgMetricBall D w r)
    (hnonneg : ∀ w z, 0 ≤ D w z) (hne : ∀ t : ℝ, 0 < t → (Λ t).Nonempty) :
    ∀ᵐ t ∂volume, 0 < t → ∀ w : ℂ, ∀ r : ℝ, Λ t ≠ lqgMetricBall D w r := by
  have hp : ∀ᵐ t ∂(μ.map τ),
      0 < t → ∀ w : ℂ, ∀ r : ℝ, Λ t ≠ lqgMetricBall D w r := by
    apply ae_map_of_countable_compact_full_cover μ τ K _ hτ hcompact hcont hfull
    intro n z hz ht w r heq
    by_cases hr : 0 < r
    · have hb : z ∈ frontier (lqgMetricBall D w r) := by
        rw [← heq]
        exact hboundary n z hz ht
      exact hpoint n z hz (τ z) ht w r hr hb heq
    · obtain ⟨x, hx⟩ := hne (τ z) ht
      have hxball : D w x < r := by
        have : x ∈ lqgMetricBall D w r := heq ▸ hx
        exact this
      exact (not_lt_of_ge (le_trans (le_of_not_gt hr) (hnonneg w x))) hxball
  rw [hmap] at hp
  have hvol := (ae_restrict_iff' measurableSet_Ioi).1 hp
  filter_upwards [hvol] with t ht hpos
  exact ht hpos hpos

end HarmonicBalls
