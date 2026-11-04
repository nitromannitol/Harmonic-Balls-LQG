import HarmonicBalls.Steps.Sec11.OdometerMaximum
import HarmonicBalls.Proofs.Sec5.RegularizedMeasure

/-!
# Regularization in the comparison chain

A null cluster boundary transfers both the local mass and the annular
complement condition from a regularized cluster to the original cluster.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- A regularized cluster and its underlying open cluster have the same mass
inside any set when the cluster boundary is null. -/
theorem measure_inter_regularizedCluster_eq {μ : Measure ℂ} {R t : ℝ} {p : ℂ}
    (hopen : IsOpen (cluster μ R p t)) (hnull : μ (frontier (cluster μ R p t)) = 0)
    (A : Set ℂ) :
    μ (A ∩ regularizedCluster μ R p t) = μ (A ∩ cluster μ R p t) := by
  symm
  apply measure_eq_measure_of_null_sdiff
    (inter_subset_inter_right A (cluster_subset_regularizedCluster hopen))
  apply measure_mono_null _ hnull
  intro x hx
  apply regularizedCluster_sdiff_subset_frontier hopen
  exact ⟨hx.1.2, fun hxcluster => hx.2 ⟨hx.1.1, hxcluster⟩⟩

/-- An annulus meeting the complement of the regularized cluster also meets
the complement of the original open cluster. -/
theorem cluster_compl_inter_nonempty_of_regularizedCluster_compl_inter_nonempty
    {μ : Measure ℂ} {R t : ℝ} {p : ℂ} (hopen : IsOpen (cluster μ R p t))
    {A : Set ℂ} (h : ((regularizedCluster μ R p t)ᶜ ∩ A).Nonempty) :
    ((cluster μ R p t)ᶜ ∩ A).Nonempty := by
  obtain ⟨x, hx, hxA⟩ := h
  exact ⟨x, fun hxc => hx (cluster_subset_regularizedCluster hopen hxc), hxA⟩

/-- The deterministic comparison chain transfers to the regularized
finite-radius cluster under the null-boundary condition. -/
theorem regularizedCluster_mass_le_of_odometer_comparison_bounds {μ : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) {R βminus βplus : ℝ} (hR : 0 < R)
    (hV : VolumeGrowth μ R βminus βplus) {p : ℂ} (hp : p ∈ ball (0 : ℂ) R)
    {t : ℝ} (ht : 0 < t) (hopen : IsOpen (cluster μ R p t))
    (hnull : μ (frontier (cluster μ R p t)) = 0)
    (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hcontain : ball z (5 * r) ⊆ ball 0 R \ {p}) (C₁ C₂ : ENNReal)
    (hmass : μ (annulus z r (2 * r) ∩ cluster μ R p t) ≤
      C₁ * (⨆ w ∈ annulus z ((1 / 2) * r) (4 * r),
        ENNReal.ofReal (odometer μ R p t w)))
    (houter : (⨆ w ∈ annulus z (4 * r) (5 * r),
        ENNReal.ofReal (odometer μ R p t w)) ≤
      C₂ * annulusGreenPotentialSup μ z (3 * r) (6 * r)) :
    μ (annulus z r (2 * r) ∩ regularizedCluster μ R p t) ≤
      (C₁ * C₂) * annulusGreenPotentialSup μ z (3 * r) (6 * r) := by
  rw [measure_inter_regularizedCluster_eq hopen hnull]
  exact annulus_mass_le_of_odometer_comparison_bounds hμ hR hV hp ht _ z hr hcontain
    C₁ C₂ hmass houter

end HarmonicBalls
