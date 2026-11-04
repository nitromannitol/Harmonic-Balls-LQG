import HarmonicBalls.Proofs.Sec5.UniformCentreExhaustion

/-! # Uniform late-time control of cluster growth

For centres in a compact subset of a disc, sufficiently late clusters are
uniformly close to the closed disc. Consequently all future clusters are
close to the current one, even after boundary contact. The time threshold
may depend on the spatial tolerance.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Pointwise

/-- For centres in a compact subset of the disc, one time threshold controls
all subsequent cluster growth at any prescribed spatial tolerance. -/
theorem uniform_centre_late_time_cluster_containment_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {K : Set (ball (0 : ℂ) R)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ z ∈ K, ∀ t : ℝ, T ≤ t → ∀ s : ℝ,
      closure (cluster μ R z s) ⊆ cluster μ R z t + ball (0 : ℂ) ε := by
  obtain ⟨T, hT, hbound⟩ :=
    uniform_centre_large_time_exhaustion_of_volumeGrowth hμ hR hV hK hε
  refine ⟨T, hT, ?_⟩
  intro z hz t ht s
  exact (closure_minimal (cluster_subset_ball.trans ball_subset_closedBall)
    isClosed_closedBall).trans (hbound z hz t ht)

universe u

/-- Almost surely, the late-time cluster-growth bound holds simultaneously
for all radii, compact sets of centres, and positive tolerances. -/
theorem ae_uniform_centre_late_time_cluster_containment
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ K : Set (ball (0 : ℂ) R), IsCompact K →
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ z ∈ K, ∀ t : ℝ, T ≤ t → ∀ s : ℝ,
        closure (cluster (μ ω) R z s) ⊆ cluster (μ ω) R z t + ball (0 : ℂ) ε := by
  filter_upwards [ae_uniform_centre_large_time_exhaustion hI2 hγ hγ2 hα hGFF hμ] with ω hω
  intro R hR K hK ε hε
  obtain ⟨T, hT, hbound⟩ := hω R hR K hK ε hε
  refine ⟨T, hT, ?_⟩
  intro z hz t ht s
  exact (closure_minimal (cluster_subset_ball.trans ball_subset_closedBall)
    isClosed_closedBall).trans (hbound z hz t ht)

end HarmonicBalls
