import HarmonicBalls.Proofs.Sec10.ComplementComponents
import HarmonicBalls.Proofs.Sec9.SharpHausdorffComparison
import HarmonicBalls.Proofs.Sec5.InteriorClusterBoundary
import HarmonicBalls.Proofs.Sec6.VolumeGrowthConsequences
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! # Null circles and cluster boundaries in a volume-growth regime

When the upper volume-growth exponent can be chosen greater than one, every
circle is null simultaneously. Combined with the good-scale boundary estimate,
this includes cluster times at which the unit circle is reached. -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Every circle in the plane has finite one-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_one_sphere_lt_top (z : ℂ) (r : ℝ) :
    Measure.hausdorffMeasure 1 (sphere z r) ≠ ∞ := by
  by_cases hr : 0 ≤ r
  · have hparam : circleMap z r '' Ioc 0 (2 * Real.pi) = sphere z r := by
      exact (image_circleMap_Ioc z r).trans (congrArg (sphere z) (abs_of_nonneg hr))
    rw [← hparam]
    have hle := (lipschitzWith_circleMap z r).hausdorffMeasure_image_le
      (d := (1 : ℝ)) (by norm_num) (Ioc (0 : ℝ) (2 * Real.pi))
    apply ne_top_of_le_ne_top _ hle
    simp only [MeasureTheory.hausdorffMeasure_real, Real.volume_Ioc, sub_zero,
      ENNReal.rpow_one]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  · rw [sphere_eq_empty_of_neg (lt_of_not_ge hr)]
    simp

universe u

/-- If the upper volume-growth threshold exceeds one, almost surely every
circle is null, simultaneously in its center and radius. -/
theorem ae_lqg_all_spheres_null_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    1 < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z : ℂ, ∀ r : ℝ, μ ω (sphere z r) = 0 := by
  intro γ α₀ hγ hγ2 hα hthreshold Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_lqgMeasure_zero_of_countable_hausdorff_cover hI2
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hzero
  intro z r
  let R := ‖z‖ + |r| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hsub : sphere z r ⊆ ball (0 : ℂ) R := by
    intro x hx
    rw [mem_ball]
    have hd := dist_triangle x z (0 : ℂ)
    have hr : dist x z = r := mem_sphere.mp hx
    rw [hr, dist_zero_right, dist_zero_right] at hd
    rw [dist_zero_right]
    dsimp [R]
    have := le_abs_self r
    linarith
  exact hzero R (sphere z r) 1 hR hsub hthreshold (fun _ => sphere z r)
    (fun x hx => mem_iUnion.mpr ⟨0, hx⟩)
    (fun _ => hausdorffMeasure_one_sphere_lt_top z r)

/-- In the same regime, the full cluster frontier is null even when the
cluster closure reaches the unit circle. -/
theorem ae_cluster_frontier_null_including_contact_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    1 < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      μ ω (frontier (cluster (μ ω) 1 z t)) = 0 := by
  intro γ α₀ hγ hγ2 hα hthreshold Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_lqg_all_spheres_null_of_volumeGrowth hI2
      γ α₀ hγ hγ2 hα hthreshold Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps
      (clusterOpenLaplacian_proved hI2)
      (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hsphere hfront
  intro t ht z hz
  exact measure_frontier_cluster_eq_zero_of_inter_ball_and_sphere
    (μ ω) z t (hfront t ht z hz) (hsphere 0 1)

/-- In the same regime, every complementary component has null frontier,
including after the cluster reaches the boundary of the unit disc. -/
theorem ae_cluster_complement_frontier_null_including_contact
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    1 < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      μ ω (frontier U) = 0 := by
  intro γ α₀ hγ hγ2 hα hthreshold Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_frontier_null_including_contact_of_volumeGrowth hI2 h82
    γ α₀ hγ hγ2 hα hthreshold Ω P hC hcirc μ hGFF hμ] with ω hfront
  intro t ht z hz U hU
  obtain ⟨x, hx, rfl⟩ := hU
  apply measure_mono_null _ (hfront t ht z hz)
  have hs := frontier_connectedComponentIn_subset_frontier
    (F := (closure (cluster (μ ω) 1 z t))ᶜ) isClosed_closure.isOpen_compl x
  rw [frontier_compl] at hs
  exact hs.trans frontier_closure_subset

end HarmonicBalls
