import HarmonicBalls.Proofs.Sec8.OriginStatementPointPolarity
import HarmonicBalls.Proofs.Sec6.GoodPrevalenceBall
import HarmonicBalls.Steps.Sec2.VolumeGrowth

/-! # Origin good scales from explicit Section 6 inputs

The imported Section 8 proof uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization of the ergodic theorem.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- Lemma 8.3 follows from the Green-potential regularity and volume-growth
statements and the displayed staged LQG inputs. -/
theorem originManyGoodScalesStmt_of_explicit_inputs
    (hholder : GreenPotentialHolderStmt.{u}) (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hatom : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ 0 hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α hC hcirc)
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureWeylScaling P γ 0 hC hcirc) : OriginManyGoodScalesStmt.{u} := by
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth
  have hCC₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc := fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc
  have hVG := Section6.veryGoodAnnulusProbabilityStmt_of_disc
    hholder hfull hgrowth hatom hAff hCC₀ hex hW
  apply originManyGoodScalesStmt_of_coordinate_change hVG hfull
  · intro Ω _ P hC hcirc _
    exact hAff Ω P hC hcirc
  · intro Ω _ P γ α hC hcirc μ _ _ _ _ _
    exact hCC Ω P γ α hC hcirc

#print axioms originManyGoodScalesStmt_of_explicit_inputs

end HarmonicBalls
