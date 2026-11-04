import HarmonicBalls.Proofs.Sec5.LocalOdometerIncrement
import HarmonicBalls.Proofs.Sec5.ClusterMassJump
import HarmonicBalls.Proofs.Sec5.BoundaryDiscontinuityCount
import HarmonicBalls.Proofs.Sec5.UniformCompactExhaustion

/-! # Continuity of interior cluster mass

Local odometer stability excludes an immediate jump in mass at every positive
time, including after the cluster meets the disc boundary.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped Pointwise ENNReal

universe u

/-- Interior mass increments converge to zero at every positive time and
for every centre simultaneously, without a compact-containment assumption. -/
theorem ae_tendsto_cluster_increment_mass_zero
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      Tendsto (fun n : ℕ => μ ω (cluster (μ ω) 1 z (t + dyadicScale n) \
        cluster (μ ω) 1 z t)) atTop (𝓝 0) := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα₀ hGFF hμ
  filter_upwards [hV, h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps h32 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_tendsto_cluster_increment_mass_of_steps h32 h33 h34 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hvol hopen hfront hlim
  intro t ht z hz
  have hzero := measure_future_cluster_sdiff_eq_zero hvol.1 zero_lt_one (hvol.2 1 zero_lt_one)
    hz ht (hfront t ht z hz) (tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds)
    (fun n => (dyadicScale_pos n).le)
  have heq := measure_future_closure_sdiff_eq_measure_future_sdiff (μ ω) (ball 0 1)
    (cluster (μ ω) 1 z t) (fun n => cluster (μ ω) 1 z (t + dyadicScale n))
    (fun _ => cluster_subset_ball)
    (fun n => (hopen (t + dyadicScale n) 1 (add_pos ht (dyadicScale_pos n))
      zero_lt_one z hz).1)
    (fun n => hfront (t + dyadicScale n) (add_pos ht (dyadicScale_pos n)) z hz)
  have h := hlim t ht z hz
  rw [heq, hzero] at h
  exact h

/-- No new interior point appears in the right limit of the closed cluster,
even after boundary contact. -/
theorem ae_future_closure_inter_ball_subset_closure
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      (⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ ball 0 1 ⊆
        closure (cluster (μ ω) 1 z t) := by
  filter_upwards [ae_tendsto_cluster_increment_mass_zero hI2 h32 h33 h34 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_future_closure_inter_ball_subset_closure_of_vanishing_increment
      hvolume h32 h33 h61 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hlim hsub
  intro t ht z hz
  apply hsub t ht z hz
  intro ε hε
  obtain ⟨n, hn⟩ := ((hlim t ht z hz).eventually
    (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
  exact ⟨n, hn.le⟩

/-- At every time, absence of new unit-circle points is sufficient for right
continuity of the closed cluster. -/
theorem ae_cluster_right_continuity_of_sphere_inclusion
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ sphere 0 1 ⊆
        closure (cluster (μ ω) 1 z t)) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
  filter_upwards [ae_tendsto_cluster_increment_mass_zero hI2 h32 h33 h34 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_cluster_right_continuity_iff_vanishing_increment_of_sphere_inclusion
      hvolume h32 h33 h34 h61 h611 h82 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ]
    with ω hlim hiff
  intro t ht z hz hsphere
  exact (hiff t ht z hz hsphere).2 (hlim t ht z hz)

/-- All right-continuity failures of a given size obey the linear bound in
the unit circle circumference, with no mass-increment condition. -/
theorem ae_encard_right_continuity_failures_le_circle_length
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, ∀ z ∈ ball (0 : ℂ) 1, ∀ d : ℝ, 0 < d →
      {t : ℝ | 0 < t ∧ t < T ∧
        ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
          closure (cluster (μ ω) 1 z s) ⊆
            cluster (μ ω) 1 z t + ball (0 : ℂ) (2 * d)}.encard ≤ ⌈2 * Real.pi / d⌉₊ := by
  filter_upwards [ae_tendsto_cluster_increment_mass_zero hI2 h32 h33 h34 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_encard_boundary_right_continuity_failures_le hvolume h32 h33 h61
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hlim hcount
  intro T z hz d hd
  apply (Set.encard_mono ?_).trans (hcount T z hz d hd)
  intro t ht
  refine ⟨ht.1, ht.2.1, ?_, ht.2.2⟩
  intro ε hε
  obtain ⟨n, hn⟩ := ((hlim t ht.1 z hz).eventually
    (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
  exact ⟨n, hn.le⟩

end HarmonicBalls
