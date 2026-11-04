import HarmonicBalls.Proofs.Sec8.OriginStatementReduction
import HarmonicBalls.Proofs.Sec6.LogAnnulusHitting

/-! # Origin good scales and Brownian point polarity

The imported Section 8 argument uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization of the ergodic theorem.
-/

open MeasureTheory

namespace HarmonicBalls

universe u

/-- Lemma 8.3 follows from the stated earlier estimates and the affine and
coordinate-change hypotheses; Brownian point avoidance is a theorem. -/
theorem originManyGoodScalesStmt_of_coordinate_change
    (hVG : VeryGoodAnnulusProbabilityStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      0 < γ → γ < 2 → α₀ < lqgQ γ →
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      LQGMeasureCoordChange P γ α₀ hC hcirc) : OriginManyGoodScalesStmt.{u} := by
  apply originManyGoodScalesStmt_of_point_avoidance_and_coordinate_change hVG hfull ?_ hAff hCC
  intro u _ x _ hxu
  exact Section6.planarBrownianMotion_point_avoidance u x hxu.symm

end HarmonicBalls
