import HarmonicBalls.Proofs.Sec8.OriginGermAssembly
/-! # Reduction of the origin good-scales statement

The imported Section 8 argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem. -/

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped Topology ProbabilityTheory NNReal
namespace HarmonicBalls
universe u
open Classical MarkovProcess in
/-- The exact Lemma 8.3 statement follows from the earlier estimates, point
avoidance, and the stated affine and coordinate-change inputs. -/
theorem originManyGoodScalesStmt_of_point_avoidance_and_coordinate_change
    (hVG : VeryGoodAnnulusProbabilityStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hpolar : ∀ u ∈ sphere (0 : ℂ) 4, ∀ x ∈ annulus (0 : ℂ) 3 5, x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      0 < γ → γ < 2 → α₀ < lqgQ γ →
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      LQGMeasureCoordChange P γ α₀ hC hcirc) : OriginManyGoodScalesStmt.{u} := by
  intro γ α₀ hγ hγ2 hα β hβ
  obtain ⟨C₃, hC₃, hC⟩ := origin_many_good_scales_of_point_avoidance hVG hfull hpolar γ α₀ hγ hγ2 hα β hβ
  refine ⟨C₃, hC₃, ?_⟩
  intro ζ hζ b hb
  obtain ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h1m, h1p, h2m, h2p, N₁, hN₁, hN⟩ := hC ζ hζ b hb
  refine ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h1m, h1p, h2m, h2p, N₁, hN₁, ?_⟩
  intro N₀ hN₀
  obtain ⟨m, hm, hM⟩ := hN N₀ hN₀
  refine ⟨m, hm, ?_⟩
  intro Ω _ P hC hcirc μ hGFF hμ
  exact hM Ω P hC hcirc μ hGFF hμ (hAff Ω P hC hcirc hGFF)
    (hCC Ω P γ α₀ hC hcirc μ hγ hγ2 hα hGFF hμ)
end HarmonicBalls
