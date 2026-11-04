import HarmonicBalls.Proofs.Sec10.PoleAvoidingGoodAnnulusDecay
import HarmonicBalls.Proofs.Sec6.AnnulusMassOdometer

/-! # Good-annulus decay from the Brownian odometer comparison -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- The good-annulus decay step follows from volume growth and Lemma 6.9. -/
theorem goodAnnulusOdometerDecayStep_of_volumeGrowth_and_harmonicMeasure
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h69 : OdometerHarmonicMeasureBoundStmt.{u}) :
    GoodAnnulusOdometerDecayStep.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hae, h69 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω hcomparison
  intro z hz t ht ρ hρ x₀ hball D hD a b r hr w hcontain hgood hmass
  have hUsub : ball x₀ ρ ⊆ ball (0 : ℂ) 1 \ {z} := ball_subset_closedBall.trans hball
  have hD' : D ∈ connectedComponentsIn (ball x₀ ρ ∩ cluster (μ ω) 1 z t) := by
    simpa [inter_comm] using hD
  obtain ⟨d, hd, hDd⟩ := hD'
  have hD' : D ∈ connectedComponentsIn (ball x₀ ρ ∩ cluster (μ ω) 1 z t) := ⟨d, hd, hDd⟩
  have hDsub : D ⊆ ball x₀ ρ ∩ cluster (μ ω) 1 z t := by
    rw [← hDd]
    exact connectedComponentIn_subset _ _
  have hzD : z ∉ D := by
    intro hzD
    exact (hUsub (hDsub hzD).1).2 (mem_singleton z)
  have hcluster := (cluster_open_laplacian_of_general greenFunctionBall
    obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
    obstacleCompatibilityShiftStep_holds hω.1 zero_lt_one (hω.2 1 zero_lt_one) hz ht).1
  have hAopen : IsOpen (annulus w (3 * r) (5 * r)) := isOpen_ball.sdiff isClosed_closedBall
  have hAsub : annulus w (3 * r) (5 * r) ⊆ ball x₀ ρ :=
    sdiff_subset.trans (ball_subset_closedBall.trans hcontain)
  have hcompactsub : closedBall w (5 * r) ⊆ ball (0 : ℂ) 1 \ {z} := hcontain.trans hUsub
  have hcont := (odometer_continuousOn_and_subharmonic hω.1 zero_lt_one
    (hω.2 1 zero_lt_one) hz ht).1
  obtain ⟨M, hM⟩ := (isCompact_closedBall w (5 * r)).bddAbove_image (hcont.mono hcompactsub)
  apply component_goodAnnulus_decay_of_harmonic_comparisons hω.1 (hω.2 1 zero_lt_one)
    hz ht isOpen_ball (hUsub.trans sdiff_subset) hD' hzD hr hcontain hgood hmass
  intro x hx
  have hxA : x ∈ annulus w (3 * r) (5 * r) := by
    have hxnorm : dist x w = 4 * r := hx.2
    constructor
    · exact (mem_ball).2 (by linarith)
    · exact fun h => by have := (mem_closedBall).1 h; linarith
  let Y := connectedComponentIn (annulus w (3 * r) (5 * r) ∩ cluster (μ ω) 1 z t) x
  have hxcluster := (hDsub hx.1).2
  have hYopen : IsOpen Y := (hAopen.inter hcluster).connectedComponentIn
  have hYsub : Y ⊆ D ∩ annulus w (3 * r) (5 * r) := by
    intro y hy
    have hyD : y ∈ D := by
      have hYsub' : Y ⊆ connectedComponentIn (ball x₀ ρ ∩ cluster (μ ω) 1 z t) x :=
        isPreconnected_connectedComponentIn.subset_connectedComponentIn
          (mem_connectedComponentIn ⟨hxA, hxcluster⟩) (by
            intro q hq
            exact ⟨hAsub (connectedComponentIn_subset _ _ hq).1,
              (connectedComponentIn_subset _ _ hq).2⟩)
      rw [← hDd] at hx
      rw [← hDd, connectedComponentIn_eq hx.1]
      exact hYsub' hy
    exact ⟨hyD, (connectedComponentIn_subset _ _ hy).1⟩
  have hfront : frontier (annulus w (3 * r) (5 * r)) ⊆ closedBall w (5 * r) :=
    frontier_subset_closure.trans (closure_minimal (sdiff_subset.trans ball_subset_closedBall) isClosed_closedBall)
  have htop : (⨆ y ∈ frontier (annulus w (3 * r) (5 * r)) ∩ closure Y,
      odometerExt (μ ω) z t y) ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (show _ ≤ ENNReal.ofReal M from ?_) ENNReal.ofReal_lt_top
    refine iSup_le fun y => iSup_le fun hy => ?_
    have hyball := hfront hy.1
    have hyz : y ≠ z := by simpa using (hcompactsub hyball).2
    simp only [odometerExt, hyz, ↓reduceIte]
    exact ENNReal.ofReal_le_ofReal (hM ⟨y, hyball, rfl⟩)
  refine ⟨Y, hYopen.measurableSet, hYsub, ?_⟩
  exact hcomparison z hz t ht _ hAopen (hAsub.trans (hUsub.trans sdiff_subset))
    (fun hzA => (hUsub (hAsub hzA)).2 (mem_singleton z)) x ⟨hxA, hxcluster⟩ Y rfl htop

end HarmonicBalls.Section6
