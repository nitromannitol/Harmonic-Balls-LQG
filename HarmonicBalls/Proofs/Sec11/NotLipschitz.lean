import HarmonicBalls.Proofs.Sec11.ConeStatement
import HarmonicBalls.Steps.Sec11.LipschitzBoundary
import HarmonicBalls.Steps.Sec11.TimeFrontierProperty

/-! # Harmonic balls are not Lipschitz domains at almost every time -/

namespace HarmonicBalls

open MeasureTheory Set Filter

universe u

/-- Proposition 11.2 follows from Lemma 11.5 by transferring the property
at typical boundary points to Lebesgue-almost every time. -/
theorem harmonicBallNotLipschitzStmt_of_noConeCondition
    (hnocone : NoConeConditionStmt.{u}) : HarmonicBallNotLipschitzStmt.{u} := by
  intro γ α₀ hγ hγ₂ hα Ω _ P hC hcirc μ hgff hμ Λ hfamily
  filter_upwards [hnocone γ α₀ hγ hγ₂ hα Ω P hC hcirc μ hgff hμ Λ hfamily,
    hμ, hfamily] with ω hpoint hμω hfamilyω
  let : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
  apply ae_time_property_of_ae_frontier (μ ω) (Λ ω) 0 hfamilyω.2
    (fun t => ¬ IsLipschitzDomain (Λ ω t))
  filter_upwards [hpoint] with z hz
  intro t ht hfrontier hLip
  exact hz t ht hfrontier (hLip.satisfiesConeCondition hfrontier)

/-- Proposition 11.2 from the annulus comparison, cone scales, and LQG volume
growth. -/
theorem harmonicBallNotLipschitzStmt_of_comparison_and_coneScales
    (hbound : AnnulusMassBoundByHarmonicChainStmt.{u})
    (hmany : ManyConeBadScalesStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) : HarmonicBallNotLipschitzStmt.{u} :=
  harmonicBallNotLipschitzStmt_of_noConeCondition
    (noConeConditionStmt_of_comparison_and_coneScales hbound hmany hgrowth)

end HarmonicBalls
