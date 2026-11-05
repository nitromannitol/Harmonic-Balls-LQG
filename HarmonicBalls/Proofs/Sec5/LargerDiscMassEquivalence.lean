import HarmonicBalls.Proofs.Sec5.MassSaturationContinuity
import HarmonicBalls.Proofs.Sec5.InteriorClusterBoundary
import HarmonicBalls.Proofs.Sec6.TranslatedCircleNull

/-! # Larger-disc closure comparison and conservation of mass -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- If the smaller cluster has null frontier, equality of nested cluster closures
and conservation of mass in the larger disc force full mass in the smaller disc. -/
theorem cluster_mass_eq_of_larger_disc_closure_eq
    {μ : Measure ℂ} {r R t : ℝ} {z : ℂ}
    (hrR : r < R) (hz : z ∈ ball (0 : ℂ) r) (ht : 0 ≤ t)
    (hsmallopen : IsOpen (cluster μ r z t)) (hlargeopen : IsOpen (cluster μ R z t))
    (hfront : μ (frontier (cluster μ r z t)) = 0)
    (heq : closure (cluster μ r z t) = closure (cluster μ R z t))
    (hmass : μ (frontier (cluster μ R z t)) = 0 →
      μ (cluster μ R z t) = ENNReal.ofReal t) :
    μ (cluster μ r z t) = ENNReal.ofReal t := by
  have hsub := cluster_subset_cluster_larger_disc (μ := μ) hrR hz ht
  have hfrontlarge : μ (frontier (cluster μ R z t)) = 0 := by
    apply measure_mono_null _ hfront
    rw [hlargeopen.frontier_eq, hsmallopen.frontier_eq, heq]
    exact sdiff_subset_sdiff_right hsub
  calc
    μ (cluster μ r z t) = μ (closure (cluster μ r z t)) :=
      (measure_closure_of_null_frontier hfront).symm
    _ = μ (closure (cluster μ R z t)) := by rw [heq]
    _ = μ (cluster μ R z t) := measure_closure_of_null_frontier hfrontlarge
    _ = ENNReal.ofReal t := hmass hfrontlarge

universe u

/-- In the unweighted whole-plane case, larger-disc closure equality is
exactly full mass, simultaneously for all centres, times and larger radii.
The interior boundary estimate is used only to establish null frontier. -/
theorem ae_larger_disc_closure_eq_iff_mass_eq
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : (0 : ℝ) < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t → ∀ R : ℝ, 1 < R →
      (closure (cluster (μ ω) 1 z t) = closure (cluster (μ ω) R z t) ↔
        μ ω (cluster (μ ω) 1 z t) = ENNReal.ofReal t) := by
  filter_upwards [clusterOpenLaplacian_proved hI2 γ 0 hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterConservationOfMass_proved hI2 γ 0 hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    lqgMeasureFullSupportStmt_of_volumeGrowth hI2 γ 0 hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps (clusterOpenLaplacian_proved hI2)
      h611 h82 γ 0 hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    Section6.ae_lqg_sphere_eq_zero_of_translation hGFF hμ hAff 0 1] with ω hopen hmass hfull hinterior hsphere
  let : (μ ω).IsOpenPosMeasure := ⟨fun U hU hne => (hfull U hU hne).ne'⟩
  intro z hz t ht R hR
  have hzR : z ∈ ball (0 : ℂ) R := ball_subset_ball hR.le hz
  have hopen1 := (hopen t 1 ht zero_lt_one z hz).1
  have hopenR := (hopen t R ht (lt_trans zero_lt_one hR) z hzR).1
  have hfront := measure_frontier_cluster_eq_zero_of_inter_ball_and_sphere
    (μ ω) z t (hinterior t ht z hz) hsphere
  constructor
  · intro heq
    apply cluster_mass_eq_of_larger_disc_closure_eq hR hz ht.le hopen1 hopenR hfront heq
    apply (hmass R t (lt_trans zero_lt_one hR) ht z hzR).2.2
    rw [← heq]
    exact (closure_minimal (cluster_subset_ball.trans ball_subset_closedBall)
      isClosed_closedBall).trans (closedBall_subset_ball hR)
  · intro h
    exact cluster_closure_eq_larger_disc_of_mass_eq hR hz ht.le hopen1 hopenR h
      (hmass R t (lt_trans zero_lt_one hR) ht z hzR).1

end HarmonicBalls
