import HarmonicBalls.Proofs.Sec10.ScalingAssembly
import HarmonicBalls.Proofs.Sec10.JordanDyadicScaling
import HarmonicBalls.Proofs.Sec9.ExistenceResultsAssembly

/-!
# Proposition 10.7 conditional export audit

The affine GFF invariance, Weyl scaling, and nonatomicity replacements used
through the imported assemblies include the Bonanno Cameron–Martin port,
consumed through Lattice-Probability. The LQG inputs below are staged and
await source review. Existence and Proposition 10.6 remain hypotheses.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- The exact frozen conclusion, with the proved affine invariance substituted. -/
theorem auditJordanExport
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hexists : ExistenceHarmonicBallsStmt.{u})
    (h10 : ComplementComponentBoundarySimpleLoopStmt.{u})
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ Λ : Ω → ℂ → ℝ → Set ℂ,
      (∀ᵐ ω ∂P, ∀ z : ℂ, IsHarmonicBallFamily (μ ω) (Λ ω z) z) →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z : ℂ,
      ∀ C ∈ connectedComponentsIn (closure (Λ ω z t))ᶜ, IsSimpleLoop (frontier C) :=
  harmonicBallComplementBoundaryJordan_of_proved_scaling hI2 hexists h10
    (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc) hCC

/-- The dyadic route removes the general coordinate-change premise. -/
theorem auditJordanExport_dyadic
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hexists : ExistenceHarmonicBallsStmt.{u})
    (h10 : ComplementComponentBoundarySimpleLoopStmt.{u}) :
    HarmonicBallComplementBoundaryJordanStmt.{u} :=
  harmonicBallComplementBoundaryJordan_of_dyadic hI2 hexists h10

/-- I2 can itself be replaced by three staged LQG inputs. -/
theorem auditJordanExport_of_staged
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ α hC hcirc)
    (hexists : ExistenceHarmonicBallsStmt.{u})
    (h10 : ComplementComponentBoundarySimpleLoopStmt.{u}) :
    HarmonicBallComplementBoundaryJordanStmt.{u} :=
  auditJordanExport_dyadic
    (lqgVolumeGrowthAllScalesStmt_of_existence hDG hCC hE) hexists h10

#print axioms auditJordanExport
#print axioms auditJordanExport_dyadic
#print axioms auditJordanExport_of_staged

end HarmonicBalls
