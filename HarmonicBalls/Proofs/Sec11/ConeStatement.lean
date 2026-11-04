import HarmonicBalls.Proofs.Sec11.ConeConclusion
import HarmonicBalls.Proofs.SecA.ObstacleNonCoincidenceHarmonic
import HarmonicBalls.Steps.Sec2.VolumeGrowth

/-! # Lemma 11.5 from cone scales and annulus comparison -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Lemma 11.5 follows from Lemmas 11.6 and 11.7 and the LQG volume
growth statement. Volume growth supplies both full support and non-atomicity. -/
theorem noConeConditionStmt_of_comparison_and_coneScales
    (hbound : AnnulusMassBoundByHarmonicChainStmt.{u})
    (hmany : ManyConeBadScalesStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) : NoConeConditionStmt.{u} := by
  intro γ α₀ hγ hγ₂ hα Ω _ P hC hcirc μ hgff hμ Λ hfamily
  have hnonatom : LQGMeasureNonatomic P γ α₀ hC hcirc := by
    intro hG hγ' hγ₂' hα' ν hν
    obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ' hγ₂' hα' hG hν
    filter_upwards [hV] with ω hV
    intro x
    have hR : 0 < ‖x‖ + 1 := by positivity
    have hx : x ∈ ball (0 : ℂ) (‖x‖ + 1) := by
      simp only [mem_ball, dist_zero_right]
      linarith
    exact (hV.2 (‖x‖ + 1) hR).measure_singleton hx
  exact ae_noConeCondition_of_comparison_and_coneScales hbound hmany
    (lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth) γ α₀ hγ hγ₂ hα
    Ω P hC hcirc μ Λ hnonatom hgff hμ hfamily

end HarmonicBalls
