import HarmonicBalls.Proofs.Sec5.IntervalRestriction

/-! # Local cluster conditions before any common containment horizon -/

namespace HarmonicBalls

universe u

open MeasureTheory Metric Set Filter

/-- Any positive time through which the clusters at all centres remain
compactly contained is a common horizon for the local cluster properties. -/
theorem ae_uniformLocalClusterProperties_of_containment
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (h32 : ClusterOpenLaplacianStmt.{u}) (h53 : ClusterBoundaryMeasureZeroStmt.{u})
    (h54 : RegularizedClusterHarmonicBallsStmt.{u}) :
    ∀ᵐ ω ∂P, ∀ H : ℝ, 0 < H →
      (∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t ∈ Ioo (0 : ℝ) H,
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 1) →
      ∀ z ∈ ball (0 : ℂ) (1 / 2),
        SatisfiesHarmonicBallConditionsOn (μ ω) (regularizedCluster (μ ω) 1 z) z H ∧
        ∀ t ∈ Ioo (0 : ℝ) H, closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 ∧
          μ ω (frontier (cluster (μ ω) 1 z t)) = 0 := by
  filter_upwards [h32 γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ,
    h53 γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ,
    h54 γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ] with ω hopen hnull hlocal
  intro H hH hbefore z hz
  have hz1 : z ∈ ball (0 : ℂ) 1 := ball_subset_ball (by norm_num) hz
  obtain ⟨T, hT, _, hconditions, htouch⟩ := hlocal z hz
  refine ⟨regularizedClusterConditionsOn_of_horizon hT hH
    (hopen T 1 hT (by norm_num) z hz1).1 (hbefore z hz) htouch hconditions, ?_⟩
  intro t ht
  exact ⟨hbefore z hz t ht, hnull z hz1 t ht.1 (hbefore z hz t ht)⟩

end HarmonicBalls
