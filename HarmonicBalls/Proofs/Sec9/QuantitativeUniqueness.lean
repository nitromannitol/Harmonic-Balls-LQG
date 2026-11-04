import HarmonicBalls.Proofs.Sec9.BoundaryExteriorDefect

/-!
# Quantitative localization from the common frontier

The mass of the common frontier bounds the mass of the part of a
subharmonic ball outside the cluster closure. Volume growth turns that
bound into a spatial estimate for points with a specified interior radius.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- A ball contained in a subharmonic ball and disjoint from the cluster
closure has mass at most that of the two common frontiers. -/
theorem IsSubharmonicBall.ball_mass_le_common_frontier
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {A : Set ℂ} {z : ℂ}
    (hA : IsSubharmonicBall μ A z) {R t βm βp : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hz : z ∈ ball (0 : ℂ) R) (hV : VolumeGrowth μ R βm βp)
    (hcl : closure A ⊆ ball 0 R) (hmass : μ A = ENNReal.ofReal t)
    (hopen : IsOpen (cluster μ R z t)) {x : ℂ} {r : ℝ}
    (hball : ball x r ⊆ A) (hdis : Disjoint (ball x r) (closure (cluster μ R z t))) :
    μ (ball x r) ≤ μ (frontier (cluster μ R z t) ∩ frontier A) := by
  have hsub := hA.cluster_subset_of_volumeGrowth hμ hR ht hV hcl hmass
  have hbound := hA.exterior_mass_le_frontier_sdiff hμ hR ht hz hV hcl hmass hopen
  rw [frontier_sdiff_eq_inter_frontier_of_subset hA.1 hsub] at hbound
  have hsubset : ball x r ⊆ A \ closure (cluster μ R z t) := by
    intro y hy
    exact ⟨hball hy, fun hyC => disjoint_left.mp hdis hy hyC⟩
  exact (measure_mono hsubset).trans hbound

/-- If the common frontier has less mass than the volume-growth lower bound
at radius `r`, every radius-`r` interior point of the comparison ball lies
within distance `r` of the cluster closure. -/
theorem IsSubharmonicBall.exists_cluster_closure_near_of_small_common_frontier
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {A : Set ℂ} {z : ℂ}
    (hA : IsSubharmonicBall μ A z) {R t βm βp : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hz : z ∈ ball (0 : ℂ) R) (hV : VolumeGrowth μ R βm βp)
    (hcl : closure A ⊆ ball 0 R) (hmass : μ A = ENNReal.ofReal t)
    (hopen : IsOpen (cluster μ R z t)) :
    ∃ r₀ > 0, ∀ r : ℝ, 0 < r → r < r₀ →
      μ (frontier (cluster μ R z t) ∩ frontier A) < ENNReal.ofReal (r ^ βm) →
      ∀ x : ℂ, ball x r ⊆ A → ∃ y ∈ closure (cluster μ R z t), dist y x < r := by
  obtain ⟨r₀, hr₀, hvol⟩ := hV.2.2
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr hrr hsmall x hball
  have hxA : x ∈ A := hball (mem_ball_self hr)
  have hxR : x ∈ ball (0 : ℂ) R := hcl (subset_closure hxA)
  by_contra hn
  have hdis : Disjoint (ball x r) (closure (cluster μ R z t)) := by
    apply disjoint_left.mpr
    intro y hy hyC
    exact hn ⟨y, hyC, mem_ball.mp hy⟩
  have hupper := hA.ball_mass_le_common_frontier hμ hR ht hz hV hcl hmass hopen hball hdis
  exact (not_lt_of_ge ((hvol r hr hrr x hxR).1.trans hupper)) hsmall

/-- On one LQG volume-growth event, the same exponent and radius work
simultaneously for all comparison balls at a fixed outer radius. -/
theorem ae_subharmonicBall_localization_of_small_common_frontier
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∃ βm : ℝ, ∀ᵐ ω ∂P, 0 < βm ∧ ∀ R : ℝ, 0 < R →
      ∃ r₀ > 0, ∀ r : ℝ, 0 < r → r < r₀ →
      ∀ (A : Set ℂ) (z : ℂ) (t : ℝ), 0 < t → z ∈ ball (0 : ℂ) R →
        closure A ⊆ ball 0 R → IsSubharmonicBall (μ ω) A z →
        μ ω A = ENNReal.ofReal t →
        μ ω (frontier (cluster (μ ω) R z t) ∩ frontier A) < ENNReal.ofReal (r ^ βm) →
        ∀ x : ℂ, ball x r ⊆ A →
          ∃ y ∈ closure (cluster (μ ω) R z t), dist y x < r := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  refine ⟨βm, ?_⟩
  filter_upwards [hV,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hV hopen
  refine ⟨(hV.2 1 zero_lt_one).1, ?_⟩
  intro R hR
  have hVR := hV.2 R hR
  obtain ⟨r₀, hr₀, hvol⟩ := hVR.2.2
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr hrr A z t ht hz hcl hA hmass hsmall x hball
  have hxR : x ∈ ball (0 : ℂ) R := hcl (subset_closure (hball (mem_ball_self hr)))
  by_contra hn
  have hdis : Disjoint (ball x r) (closure (cluster (μ ω) R z t)) := by
    apply disjoint_left.mpr
    intro y hy hyC
    exact hn ⟨y, hyC, mem_ball.mp hy⟩
  have hupper := hA.ball_mass_le_common_frontier hV.1 hR ht hz hVR hcl hmass
    (hopen t R ht hR z hz).1 hball hdis
  exact (not_lt_of_ge ((hvol r hr hrr x hxR).1.trans hupper)) hsmall

end HarmonicBalls
