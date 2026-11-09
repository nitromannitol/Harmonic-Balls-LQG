import HarmonicBalls.Assembly.ExistenceUniqueness
import HarmonicBalls.Assembly.Novelty
import HarmonicBalls.Proofs.Sec1.LocalityCompatibilityAssembly
import HarmonicBalls.Proofs.Sec10.PrevalenceCrossingAssembly
import HarmonicBalls.Proofs.Sec10.ScalingAssembly
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.Draft.Section2
import HarmonicBalls.Draft.Section5
import HarmonicBalls.Draft.Section10
import HarmonicBalls.Draft.Section11

/-!
# FIRST PASS, Sections 1 and 10 (worker n1)

Each theorem `firstPass_<section>_<number>` has as conclusion the Draft statement of the numbered result
(or its corrected form) and as hypotheses only:
* Draft statements of other numbered results used by the printed proof (`Draft/Section*.lean`), and
* external inputs: the Proposed statements of `Proposed/LQG.lean` (pending operator source-check).

No new mathematics is proved in this file for the results below: each is a composition of committed reductions
(`Assembly/`, `Proofs/Sec1`, `Proofs/Sec10`). Hypotheses are kept at the printed quantifier order and carrier.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- FIRST PASS, Theorem 1.1 (theorem:harmonic-balls). Existence (Theorem 5.5) and uniqueness (Proposition 5.6) of
the family of harmonic balls, assembled by `existenceUniquenessHarmonicBallsStmt_of_sec5`. -/
theorem firstPass_1_1
    (h55 : ExistenceHarmonicBallsStmt.{u}) (h56 : UniquenessHarmonicBallsStmt.{u}) :
    ExistenceUniquenessHarmonicBallsStmt.{u} :=
  existenceUniquenessHarmonicBallsStmt_of_sec5 h55 h56

/-- FIRST PASS, Theorem 1.2 (theorem:harmonic-balls-properties). The Jordan clause is Proposition 10.7; the
non-Lipschitz and non-metric-ball clauses are the Section 11 statements, taken as hypotheses. The family at the
origin is extended to all centres through Theorem 1.1 (`harmonicBallNoveltyStmt_of_existence_and_results`). -/
theorem firstPass_1_2
    (h55 : ExistenceHarmonicBallsStmt.{u}) (h56 : UniquenessHarmonicBallsStmt.{u})
    (hjordan : HarmonicBallComplementBoundaryJordanStmt.{u})
    (hlip : HarmonicBallNotLipschitzStmt.{u})
    (hmetric : HarmonicBallNotMetricBallStmt.{u}) :
    HarmonicBallNoveltyStmt.{u} :=
  harmonicBallNoveltyStmt_of_existence_and_results (firstPass_1_1 h55 h56) hjordan hlip hmetric

/-- FIRST PASS, Proposition 1.3 (prop:locally-determined). Closed harmonic balls are local sets for the field,
from volume growth (Section 2), Theorem 5.5, Proposition 5.6 and locality of the LQG measure (Proposed input). -/
theorem firstPass_1_3
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h55 : ExistenceHarmonicBallsStmt.{u}) (h56 : UniquenessHarmonicBallsStmt.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureLocality P γ α₀ hC hcirc) :
    HarmonicBallLocalSetStmt.{u} :=
  harmonicBallLocalSet_of_volumeGrowth_existence_uniqueness_and_measureLocality hI2 h55 h56 hmeasure

/-- FIRST PASS, Lemma 10.1 (lemma:cannot-cross). Deterministic bound `⌈1/α⌉` on the number of crossing components,
from the volume growth of Section 2 and zero-strength existence of the LQG measure (Proposed input). -/
theorem firstPass_10_1
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc) :
    ClusterBoundedCrossingsStmt.{u} :=
  clusterBoundedCrossings_of_volumeGrowth_and_zero_existence hI2 hE0

/-- FIRST PASS, Proposition 10.7 (prop:boundary-simple-loop-full-cluster), corrected as [C50]: pathwise dyadic
rescaling of Proposition 10.6 (`harmonicBallComplementBoundaryJordan_of_proved_scaling`). The affine invariance
and coordinate-change inputs are Proposed. -/
theorem firstPass_10_7
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h55 : ExistenceHarmonicBallsStmt.{u})
    (h10 : ComplementComponentBoundarySimpleLoopStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    HarmonicBallComplementBoundaryJordanStmt.{u} :=
  harmonicBallComplementBoundaryJordan_of_proved_scaling hI2 h55 h10 hAff hCC

#print axioms firstPass_1_1
#print axioms firstPass_1_2
#print axioms firstPass_1_3
#print axioms firstPass_10_1
#print axioms firstPass_10_7

end HarmonicBalls
