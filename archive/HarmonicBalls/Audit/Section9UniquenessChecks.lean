import HarmonicBalls.Proofs.Sec9.ObstacleComparison
import HarmonicBalls.Proofs.Sec9.WeakUniqueness
import HarmonicBalls.Proofs.Sec9.DyadicGlobalUniqueness
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly

/-!
# Section 9 uniqueness: current-export checks

Typed examples that instantiate the existing Section 9 producers at their literal types. Every explicit
premise is a binder of the example; no hypothesis is added and no carrier is changed. The `#print axioms`
lines record the axioms each producer depends on; only the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) are expected. Compiling this file is not closure of any numbered result: the remaining premises
are the binders below.

Credit: the imported Section 6 and Section 8 proofs consume Leonardo Bonanno's work in `LatticeProb.Bonanno`
and `LatticeProb.Prob.Birkhoff`; this file inherits that dependency through its imports.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

-- Lemma 9.1 (`ObstacleComparisonStmt`, frozen): its producer has no premises.
example : ObstacleComparisonStmt := obstacleComparison

-- Deterministic weak Proposition 9.2 at its literal type. Lemma 9.1(1) enters through
-- `IsSubharmonicBall.neg_greenPotential_mem_supersolutions`; the premises are local finiteness of `μ`,
-- volume growth at radius `R`, openness of the cluster and conservation of its mass.
example {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {A : Set ℂ} {z : ℂ}
    (hA : IsSubharmonicBall μ A z) {R t βm βp : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hV : VolumeGrowth μ R βm βp) (hcl : closure A ⊆ ball (0 : ℂ) R)
    (hmass : μ A = ENNReal.ofReal t) (hopen : IsOpen (cluster μ R z t))
    (hcluster : μ (cluster μ R z t) = ENNReal.ofReal t) :
    cluster μ R z t ⊆ A ∧ μ (A \ regularizedCluster μ R z t) = 0 :=
  hA.weak_uniqueness_of_volumeGrowth hμ hR ht hV hcl hmass hopen hcluster

-- Frozen weak Proposition 9.2 (`SubharmonicBallUniquenessWeakStmt`) from I2 and the all-radii step.
example (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hboundary : ClusterBoundaryNullAllRadii.{u}) :
    SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_boundaryNull hI2 hboundary

-- Top-level frozen export: its only premises are I2 and Lemma 8.2 (`TypicalPointManyGoodScalesStmt`).
example (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_volumeGrowth_typicalScales hI2 h82

-- Predecessor of the all-radii step: Lemma 6.11 (`h611`) and Lemma 8.2 (`h82`) are explicit premises,
-- and the affine-invariance premise is the ∀-statement `hAff`.
example (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc) :
    ClusterBoundaryNullAllRadii.{u} :=
  clusterBoundaryNullAllRadii_of_dyadic_typical_scales hI2 h611 h82 hAff

-- The affine-invariance premise is discharged from the covariance field of `IsWholePlaneGFF`.
example : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc :=
  fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc

end HarmonicBalls
