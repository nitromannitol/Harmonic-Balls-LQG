import HarmonicBalls.Proofs.Sec2.Assembly
import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import HarmonicBalls.Proofs.Sec3.ConservationOfMassLemma
import HarmonicBalls.Proofs.Sec6.Section6LiteratureAssembly
import HarmonicBalls.Proofs.Sec7.ClusterUpperBound
import HarmonicBalls.Proofs.Sec7.ClusterContinuity
import HarmonicBalls.Proofs.Sec8.ClusterBoundary

/-! # Section 7 from Green-potential regularity and LQG inputs

The Section 6 annulus iteration uses Leonardo Bonanno's proof of the
Gwynne–Miller lemma in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
The displayed LQG inputs are staged and await source review.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

section

variable
  (hholder : GreenPotentialHolderStmt.{u})
  (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    WholePlaneGFFAffineInvariance P hC hcirc)
  (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureCoordChange P γ 0 hC hcirc)
  (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureWeylScaling P γ 0 hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureExistence P γ 0 hC hcirc)
  (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureNonatomic P γ α₀ hC hcirc)

include hholder hDG hAff hCC hW hE hN

/-- Proposition 7.1 from the Green-potential clause of Proposition 2.5
and the displayed staged whole-plane LQG inputs. -/
theorem clusterUpperBoundPolyHighProb_of_literature :
    ClusterUpperBoundPolyHighProbStmt.{u} := by
  have hgrowth := lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC hW hE hN
  have hvolume := liouvilleVolumeGrowthStmt_of_literature hDG hAff hCC hW hE hN
  have h61 := (Section6.section6_of_greenPotential_and_literature
    hholder hDG hAff hCC hW hE hN).1
  exact clusterUpperBoundPolyHighProb_of_steps hvolume (clusterOpenLaplacian_proved hgrowth)
    (clusterConservationOfMass_proved hgrowth) h61

/-- Proposition 8.1 and Proposition 7.2 from Lemma 8.2, the Green-potential
clause of Proposition 2.5, and the displayed staged whole-plane LQG inputs. -/
theorem clusterBoundary_and_timeContinuity_of_literature
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    BoundaryMeasureZeroOfCompactClusterStmt.{u} ∧ ClusterTimeContinuityStmt.{u} := by
  have hgrowth := lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC hW hE hN
  have hvolume := liouvilleVolumeGrowthStmt_of_literature hDG hAff hCC hW hE hN
  have h61 := (Section6.section6_of_greenPotential_and_literature
    hholder hDG hAff hCC hW hE hN).1
  have h32 := clusterOpenLaplacian_proved hgrowth
  have h81 := boundaryMeasureZeroOfCompactClusterStmt_of_steps h32
    (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hgrowth) h82
  exact ⟨h81, clusterTimeContinuity_of_steps hvolume h32 (clusterMonotone_proved hgrowth)
    (clusterConservationOfMass_proved hgrowth) h61 h81⟩

end

#print axioms clusterUpperBoundPolyHighProb_of_literature
#print axioms clusterBoundary_and_timeContinuity_of_literature

end HarmonicBalls
