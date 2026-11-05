import HarmonicBalls.Proofs.Sec5.InteriorTimeContinuity
import HarmonicBalls.Proofs.Sec5.BoundaryContinuityCompactness

/-! # Interior balls and boundary continuity

Uniform interior balls near a possible new boundary point, together with
vanishing mass increments, exclude that point. The interior-ball condition
is a sufficient geometric condition; it is not established here for LQG
clusters.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped Pointwise ENNReal

/-- If future sets have uniformly sized interior balls near every point of
an indicated set, vanishing mass increments exclude new points there. -/
theorem future_closure_inter_subset_of_interior_ball
    {μ : Measure ℂ} {βm βp : ℝ} (hV : VolumeGrowth μ 1 βm βp)
    {A : Set ℂ} {B : ℕ → Set ℂ} {S : Set ℂ}
    (hmass : Tendsto (fun n => μ (B n \ A)) atTop (𝓝 0))
    (hball : ∀ x ∈ S, x ∉ closure A → ∀ d : ℝ, 0 < d → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ n, x ∈ closure (B n) → ∃ y ∈ ball (0 : ℂ) 1,
        ball y ρ ⊆ B n ∩ ball x d) :
    (⋂ n, closure (B n)) ∩ S ⊆ closure A := by
  intro x hx
  by_contra hxA
  obtain ⟨d, hd, hdsub⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl x hxA
  obtain ⟨ρ, hρ, hρball⟩ := hball x hx.2 hxA d hd
  obtain ⟨r₀, hr₀, hvol⟩ := hV.2.2
  let r := min ρ r₀ / 2
  have hr : 0 < r := half_pos (lt_min hρ hr₀)
  have hrρ : r ≤ ρ := by dsimp [r]; linarith [min_le_left ρ r₀]
  have hrr₀ : r < r₀ := by dsimp [r]; linarith [min_le_right ρ r₀]
  have hpos : 0 < ENNReal.ofReal (r ^ βm) :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hr _)
  obtain ⟨n, hn⟩ := (hmass.eventually (Iio_mem_nhds hpos)).exists
  obtain ⟨y, hy, hsub⟩ := hρball n (mem_iInter.mp hx.1 n)
  have hballsub : ball y r ⊆ B n \ A := by
    intro w hw
    have hw' := hsub (ball_subset_ball hrρ hw)
    exact ⟨hw'.1, fun hwA => (hdsub hw'.2) (subset_closure hwA)⟩
  have hlow := (hvol r hr hrr₀ y hy).1
  exact (not_le_of_gt hn) (hlow.trans (measure_mono hballsub))

/-- The boundary interior-ball condition and vanishing mass increments imply
right continuity once interior right-limit points have been excluded. -/
theorem cluster_right_continuity_of_boundary_interior_ball
    {μ : Measure ℂ} {βm βp : ℝ} (hV : VolumeGrowth μ 1 βm βp)
    {z : ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → cluster μ 1 z s ⊆ cluster μ 1 z s')
    (hmass : Tendsto (fun n : ℕ => μ (cluster μ 1 z (t + dyadicScale n) \
      cluster μ 1 z t)) atTop (𝓝 0))
    (hinter : (⋂ n : ℕ, closure (cluster μ 1 z (t + dyadicScale n))) ∩ ball 0 1 ⊆
      closure (cluster μ 1 z t))
    (hball : ∀ x ∈ sphere (0 : ℂ) 1, x ∉ closure (cluster μ 1 z t) →
      ∀ d : ℝ, 0 < d → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ n, x ∈ closure (cluster μ 1 z (t + dyadicScale n)) →
        ∃ y ∈ ball (0 : ℂ) 1, ball y ρ ⊆ cluster μ 1 z (t + dyadicScale n) ∩ ball x d) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (cluster μ 1 z s) ⊆ cluster μ 1 z t + ball (0 : ℂ) ε := by
  apply (cluster_closure_dyadic_iInter_subset_iff_right_continuous ht hmono).mp
  intro x hx
  have hclosed : x ∈ closedBall (0 : ℂ) 1 :=
    (closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall)
      (mem_iInter.mp hx 0)
  by_cases hxball : x ∈ ball (0 : ℂ) 1
  · exact hinter ⟨hx, hxball⟩
  · have hxsphere : x ∈ sphere (0 : ℂ) 1 := by
      apply mem_sphere.mpr
      exact le_antisymm (mem_closedBall.mp hclosed)
        (le_of_not_gt (by simpa only [mem_ball] using hxball))
    exact future_closure_inter_subset_of_interior_ball hV hmass hball ⟨hx, hxsphere⟩

universe u

/-- Almost surely, the boundary interior-ball condition suffices for right
continuity at any positive time. The condition itself remains unproved. -/
theorem ae_cluster_right_continuity_of_boundary_interior_ball
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      (∀ x ∈ sphere (0 : ℂ) 1, x ∉ closure (cluster (μ ω) 1 z t) →
        ∀ d : ℝ, 0 < d → ∃ ρ : ℝ, 0 < ρ ∧
        ∀ n, x ∈ closure (cluster (μ ω) 1 z (t + dyadicScale n)) →
          ∃ y ∈ ball (0 : ℂ) 1,
            ball y ρ ⊆ cluster (μ ω) 1 z (t + dyadicScale n) ∩ ball x d) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα₀ hGFF hμ
  filter_upwards [hV, h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_tendsto_cluster_increment_mass_zero hI2 h32 h33 h34 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_future_closure_inter_ball_subset_closure hI2 hvolume h32 h33 h34 h61 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hvol hmono hmass hinter
  intro z hz t ht hball
  exact cluster_right_continuity_of_boundary_interior_ball (hvol.2 1 zero_lt_one) ht
    (fun s s' hs hss' => hmono s s' 1 hs hss' zero_lt_one z hz)
    (hmass t ht z hz) (hinter t ht z hz) hball

#print axioms ae_cluster_right_continuity_of_boundary_interior_ball
#print axioms future_closure_inter_subset_of_interior_ball
#print axioms cluster_right_continuity_of_boundary_interior_ball

end HarmonicBalls
