import HarmonicBalls.Proofs.Sec8.CenteredCircleLocal
import HarmonicBalls.Proofs.Sec8.ContinuityExhaustion

/-! # Origin good-scale assembly

The local centered-circle versions follow from the whole-plane GFF covariance.
The imported Section 8 argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped Topology ProbabilityTheory NNReal

namespace HarmonicBalls

universe u

open Classical MarkovProcess in
/-- Uniform origin good-scale parameters, conditional on point avoidance and
triviality of the whole-plane field germ. -/
theorem origin_many_good_scales_of_field_germ_trivial
    (hVG : VeryGoodAnnulusProbabilityStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hpolar : ∀ u ∈ sphere (0 : ℂ) 4, ∀ x ∈ annulus (0 : ℂ) 3 5, x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ β : ℝ, (2 + γ) ^ 2 / 2 < β →
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ ζ : ℝ, 0 < ζ → ∀ b ∈ Ioo (0 : ℝ) 1,
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
    ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ N₀ : ℕ, N₁ ≤ N₀ → ∃ m : ℝ, 0 < m ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      WholePlaneGFFAffineInvariance P hC hcirc → LQGMeasureCoordChange P γ α₀ hC hcirc →
      (∀ A : Set Ω, (∀ ε, 0 < ε →
        MeasurableSet[Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)] A) →
        P A = 0 ∨ P A = 1) →
      ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
        (1 - ζ) * (N : ℝ) ≤ veryGoodComparableScaleCount (μ ω) β 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ m N := by
  intro γ α₀ hγ hγ2 hα β hβ
  obtain ⟨C₃, hC₃, hC⟩ :=
    origin_many_good_scales_of_centered_circle_versions hVG hfull hpolar γ α₀ hγ hγ2 hα β hβ
  refine ⟨C₃, hC₃, ?_⟩
  intro ζ hζ b hb
  obtain ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h1m, h1p, h2m, h2p, N₁, hN₁, hN⟩ := hC ζ hζ b hb
  refine ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h1m, h1p, h2m, h2p, N₁, hN₁, ?_⟩
  intro N₀ hN₀
  obtain ⟨m, hm, hM⟩ := hN N₀ hN₀
  refine ⟨m, hm, ?_⟩
  intro Ω _ P hC hcirc μ hGFF hμ hAff hCC htrivial
  apply hM Ω P hC hcirc μ hGFF hμ hAff hCC ?_ htrivial
  intro ε _ n
  exact hGFF.exists_joint_centered_circle_version (α₀ := α₀) (ε := ε) (dyadicScale_pos n)

end HarmonicBalls
