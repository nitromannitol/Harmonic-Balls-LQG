import HarmonicBalls.Proofs.Sec9.BoundaryScaleField
import HarmonicBalls.Proofs.Sec5.SupersolutionScaling
import HarmonicBalls.Proofs.Sec2.Assembly

/-!
# Weak uniqueness with proved cluster scaling

The field invariance and LQG coordinate-change assumptions are staged
literature inputs pending source review.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- Weak Proposition 9.2 from volume growth, Proposition 8.1 and the staged
field invariance and coordinate-change inputs. -/
theorem subharmonicBallUniquenessWeak_of_proved_scaling
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h8 : BoundaryMeasureZeroOfCompactClusterStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_scaledField hI2 h8
    clusterPathwiseScaleStep_proved hAff hCC

/-- Weak Proposition 9.2 with volume growth supplied by the six staged
literature inputs from Section 2. Proposition 8.1 remains a hypothesis. -/
theorem subharmonicBallUniquenessWeak_of_literature_and_boundary
    (h8 : BoundaryMeasureZeroOfCompactClusterStmt.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ α₀ hC hcirc) :
    SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_proved_scaling
    (lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff (fun Ω _ P γ hC hcirc =>
      hCC Ω P γ 0 hC hcirc) hW hE hN) h8 hAff hCC

end HarmonicBalls
