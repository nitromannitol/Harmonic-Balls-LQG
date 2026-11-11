import HarmonicBalls.Proofs.Sec5.UniformCentreExhaustion
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! # Uniform late-time Hausdorff bounds -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Pointwise

/-- Clusters with centres in a compact subset of a disc form a uniform
Hausdorff-Cauchy family as their times tend to infinity. -/
theorem uniform_centre_late_time_hausdorff_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {K : Set (ball (0 : ℂ) R)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ z ∈ K, ∀ w ∈ K, ∀ s t : ℝ, T ≤ s → T ≤ t →
      hausdorffEDist (closure (cluster μ R z s)) (closure (cluster μ R w t)) ≤
        ENNReal.ofReal ε := by
  obtain ⟨T, hT, hcover⟩ := uniform_centre_large_time_exhaustion_of_volumeGrowth
    hμ hR hV hK hε
  refine ⟨T, hT, ?_⟩
  intro z hz w hw s t hs ht
  have hclosed : ∀ (z : ball (0 : ℂ) R) (t : ℝ),
      closure (cluster μ R z t) ⊆ closedBall (0 : ℂ) R := by
    intro z t
    exact closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
  have hnear (x : ℂ) (hx : x ∈ closedBall (0 : ℂ) R)
      (z : ball (0 : ℂ) R) (hz : z ∈ K) (t : ℝ) (ht : T ≤ t) :
      ∃ y ∈ closure (cluster μ R z t), edist x y ≤ ENNReal.ofReal ε := by
    obtain ⟨y, hy, v, hv, hxy⟩ := hcover z hz t ht hx
    refine ⟨y, subset_closure hy, ?_⟩
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    rw [← hxy, dist_eq_norm]
    have hv' : ‖v‖ < ε := mem_ball_zero_iff.mp hv
    simpa using hv'.le
  apply hausdorffEDist_le_of_mem_edist
  · intro x hx
    exact hnear x (hclosed z s hx) w hw t ht
  · intro x hx
    exact hnear x (hclosed w t hx) z hz s hs

/-- For each tolerance, one late time makes every future cluster lie within
that tolerance of every cluster centred in the prescribed compact set. -/
theorem uniform_centre_late_time_future_bound_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {K : Set (ball (0 : ℂ) R)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ z ∈ K, ∀ w : ball (0 : ℂ) R, ∀ t : ℝ, T ≤ t →
      ∀ s : ℝ, closure (cluster μ R w s) ⊆ cluster μ R z t + ball (0 : ℂ) ε := by
  obtain ⟨T, hT, hcover⟩ := uniform_centre_large_time_exhaustion_of_volumeGrowth
    hμ hR hV hK hε
  refine ⟨T, hT, ?_⟩
  intro z hz w t ht s
  exact (closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall).trans
    (hcover z hz t ht)

universe u

/-- The late-time Hausdorff bound holds almost surely and simultaneously for
all radii and compact subsets of centres for an LQG measure. -/
theorem ae_uniform_centre_late_time_hausdorff
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ K : Set (ball (0 : ℂ) R), IsCompact K →
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ z ∈ K, ∀ w ∈ K,
        ∀ s t : ℝ, T ≤ s → T ≤ t →
          hausdorffEDist (closure (cluster (μ ω) R z s))
            (closure (cluster (μ ω) R w t)) ≤ ENNReal.ofReal ε := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hω
  intro R hR K hK ε hε
  exact uniform_centre_late_time_hausdorff_of_volumeGrowth hω.1 hR (hω.2 R hR) hK hε

/-- Almost surely, the late-time future bound is uniform over every compact
set of centres and every radius. -/
theorem ae_uniform_centre_late_time_future_bound
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ K : Set (ball (0 : ℂ) R), IsCompact K →
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ z ∈ K, ∀ w : ball (0 : ℂ) R,
        ∀ t : ℝ, T ≤ t → ∀ s : ℝ,
          closure (cluster (μ ω) R w s) ⊆ cluster (μ ω) R z t + ball (0 : ℂ) ε := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hω
  intro R hR K hK ε hε
  exact uniform_centre_late_time_future_bound_of_volumeGrowth hω.1 hR (hω.2 R hR) hK hε

end HarmonicBalls
