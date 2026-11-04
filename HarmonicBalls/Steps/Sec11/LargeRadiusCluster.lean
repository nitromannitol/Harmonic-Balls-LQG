import HarmonicBalls.Steps.Sec11.RegularizedComparison

/-!
# Large finite-radius representatives of regularized clusters

For a fixed time the whole-plane cluster has a representative in every
sufficiently large disk. The original cluster is open and is compactly
contained in that disk.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- A regularized cluster family has an open, compactly contained original
cluster representative in an arbitrarily large disk. -/
theorem IsRegularizedClusterFamily.exists_large_cluster_representative
    {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {p : ℂ}
    (hfam : IsRegularizedClusterFamily μ Λ p) {t : ℝ} (ht : 0 < t)
    (hμ : IsLocallyFiniteMeasure μ) {βminus βplus : ℝ}
    (hV : ∀ R : ℝ, 0 < R → VolumeGrowth μ R βminus βplus) (K : ℝ) :
    ∃ R : ℝ, K < R ∧ 0 < R ∧ p ∈ ball 0 R ∧
      IsOpen (cluster μ R p t) ∧ closure (cluster μ R p t) ⊆ ball 0 R ∧
      Λ t = regularizedCluster μ R p t := by
  obtain ⟨s, hs⟩ := ((hfam.1.isBounded t ht).closure).subset_ball (0 : ℂ)
  let R := max 1 (max s K) + 1
  have hR : 0 < R := by dsimp [R]; have := le_max_left (1 : ℝ) (max s K); linarith
  have hsR : s ≤ R := by
    have := (le_max_left s K).trans (le_max_right (1 : ℝ) (max s K))
    dsimp [R]; linarith
  have hKR : K < R := by
    have := (le_max_right s K).trans (le_max_right (1 : ℝ) (max s K))
    dsimp [R]; linarith
  have hΛR : closure (Λ t) ⊆ ball (0 : ℂ) R := hs.trans (ball_subset_ball hsR)
  have hpR : p ∈ ball (0 : ℂ) R := hΛR (subset_closure (hfam.1.mem t ht))
  have heq := hfam.2.2 t ht R hR hΛR R le_rfl
  have hshift := obstacleCompatibilityShiftStep_holds μ hμ R βminus βplus hR (hV R hR) p hpR t ht
  have hopen : IsOpen (cluster μ R p t) := by
    rw [hshift.2.2.1]
    exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds
      hμ hR (hV R hR) hpR ht
  have hsub : cluster μ R p t ⊆ Λ t := by
    rw [heq]
    exact cluster_subset_regularizedCluster hopen
  exact ⟨R, hKR, hR, hpR, hopen, (closure_mono hsub).trans hΛR, heq⟩

/-- The finite-radius comparison chain transfers to a whole-plane regularized
cluster family. The all-radius comparison bounds and boundary-nullity remain
explicit hypotheses. -/
theorem IsRegularizedClusterFamily.annulus_mass_le_of_comparison_bounds
    {μ : Measure ℂ} {Λ : ℝ → Set ℂ} (hfam : IsRegularizedClusterFamily μ Λ 0)
    {t : ℝ} (ht : 0 < t) (hμ : IsLocallyFiniteMeasure μ) {βminus βplus : ℝ}
    (hV : ∀ R : ℝ, 0 < R → VolumeGrowth μ R βminus βplus)
    (hnull : ∀ R : ℝ, 0 < R → closure (cluster μ R 0 t) ⊆ ball 0 R →
      μ (frontier (cluster μ R 0 t)) = 0)
    (z : ℂ) {r : ℝ} (hr : 0 < r) (havoid : (0 : ℂ) ∉ closedBall z (10 * r))
    (hbad : (annulus z (4 * r) (5 * r) ∩ (Λ t)ᶜ).Nonempty) (C₁ C₂ : ℝ≥0∞)
    (hmass : ∀ R : ℝ, 0 < R → closedBall z (6 * r) ⊆ ball 0 R \ {(0 : ℂ)} →
      μ (annulus z r (2 * r) ∩ cluster μ R 0 t) ≤
      C₁ * (⨆ w ∈ annulus z ((1 / 2) * r) (4 * r), ENNReal.ofReal (odometer μ R 0 t w)))
    (houter : ∀ R : ℝ, 0 < R → closedBall z (6 * r) ⊆ ball 0 R \ {(0 : ℂ)} →
      ((cluster μ R 0 t)ᶜ ∩ annulus z (4 * r) (5 * r)).Nonempty →
      (⨆ w ∈ annulus z (4 * r) (5 * r), ENNReal.ofReal (odometer μ R 0 t w)) ≤
        C₂ * annulusGreenPotentialSup μ z (3 * r) (6 * r)) :
    μ (annulus z r (2 * r) ∩ Λ t) ≤
      (C₁ * C₂) * annulusGreenPotentialSup μ z (3 * r) (6 * r) := by
  obtain ⟨R, hlarge, hR, hp, hopen, hcompact, heq⟩ :=
    hfam.exists_large_cluster_representative ht hμ hV (‖z‖ + 6 * r)
  have hclosed : closedBall z (6 * r) ⊆ ball (0 : ℂ) R \ {(0 : ℂ)} := by
    intro x hx
    constructor
    · rw [mem_ball_zero_iff]
      have hx' : ‖x - z‖ ≤ 6 * r := by simpa only [mem_closedBall, dist_eq_norm] using hx
      calc ‖x‖ = ‖(x - z) + z‖ := by congr 1; abel
        _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
        _ < R := by linarith
    · intro hx0
      have hx0' : x = 0 := hx0
      subst x
      apply havoid
      exact (closedBall_subset_closedBall (by linarith : 6 * r ≤ 10 * r)) hx
  have hcontain : ball z (5 * r) ⊆ ball (0 : ℂ) R \ {(0 : ℂ)} :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith : 5 * r ≤ 6 * r))).trans hclosed
  have hbad' : ((cluster μ R 0 t)ᶜ ∩ annulus z (4 * r) (5 * r)).Nonempty := by
    have hbad'' : ((regularizedCluster μ R 0 t)ᶜ ∩ annulus z (4 * r) (5 * r)).Nonempty := by
      rw [← heq, inter_comm]
      exact hbad
    exact cluster_compl_inter_nonempty_of_regularizedCluster_compl_inter_nonempty hopen hbad''
  rw [heq]
  exact regularizedCluster_mass_le_of_odometer_comparison_bounds hμ hR (hV R hR) hp ht
    hopen (hnull R hR hcompact) z hr hcontain C₁ C₂ (hmass R hR hclosed) (houter R hR hclosed hbad')

end HarmonicBalls
