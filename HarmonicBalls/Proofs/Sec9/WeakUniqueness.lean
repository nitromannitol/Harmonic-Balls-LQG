import HarmonicBalls.Proofs.Sec9.SubharmonicSupersolution
import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import HarmonicBalls.Proofs.Sec3.ConservationOfMassLemma

/-!
# Weak Proposition 9.2 from boundary nullity at all radii

The remaining step is the all-radii form of Proposition 8.1. That proposition is currently
stated only for the unit disc; the comparison proof below needs one event valid for all radii.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- The all-radii, simultaneous-centre form of Proposition 8.1 needed for Proposition 9.2.
This is a proof step, not a literature input. -/
def ClusterBoundaryNullAllRadii : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ R t : ℝ, 0 < R → 0 < t → ∀ z ∈ ball (0 : ℂ) R,
    closure (cluster (μ ω) R z t) ⊆ ball 0 R → μ ω (frontier (cluster (μ ω) R z t)) = 0

/-- Weak Proposition 9.2 from volume growth and the all-radii boundary-nullity step. -/
theorem subharmonicBallUniquenessWeak_of_boundaryNull
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hboundary : ClusterBoundaryNullAllRadii.{u}) :
    SubharmonicBallUniquenessWeakStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hboundary γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω hopen hmass hbound
  intro A z t R ht hR hz hcl hA hA_mass
  have hsub := hA.cluster_subset_of_volumeGrowth hω.1 hR ht (hω.2 R hR) hcl hA_mass
  have hcompact : closure (cluster (μ ω) R z t) ⊆ ball 0 R := (closure_mono hsub).trans hcl
  have hzero := hbound R t hR ht z hz hcompact
  have hcluster := (hmass R t hR ht z hz).2.2 hcompact hzero
  exact hA.weak_uniqueness_of_volumeGrowth hω.1 hR ht (hω.2 R hR) hcl hA_mass
    (hopen t R ht hR z hz).1 hcluster

end HarmonicBalls
