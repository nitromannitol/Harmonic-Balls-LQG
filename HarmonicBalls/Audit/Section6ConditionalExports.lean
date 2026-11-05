import HarmonicBalls.Proofs.Sec6.SevenAdicFineSupportPrevalence

/-! # Conditional Section 6 export checks

These examples check the four exact frozen proposition-valued conclusions with
both external premises displayed; existence is expanded to its defining type.
They do not establish either premise or approve the mathematical sources.
The imported annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`; its field-law bridge uses
`LatticeProb.Bonanno.LQGMetric.Field.GFFLaw`,
`LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate`, and
`LatticeProb.Bonanno.LQGMetric.Field.ExistGFF`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory

universe u

example (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → 0 < lqgQ γ →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ) :
    ManyGoodAnnuliStmt.{u} :=
  manyGoodAnnuliStmt_of_volumeGrowth_zero_existence hgrowth hex

example (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → 0 < lqgQ γ →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ) :
    ManyVeryGoodAnnuliStmt.{u} :=
  manyVeryGoodAnnuliStmt_of_volumeGrowth_zero_existence hgrowth hex

example (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → 0 < lqgQ γ →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ) :
    HarnackTypeComponentStmt.{u} :=
  harnackTypeComponentStmt_of_volumeGrowth_zero_existence hgrowth hex

example (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → 0 < lqgQ γ →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ) :
    HarnackTypeEstimateStmt.{u} :=
  harnackTypeEstimateStmt_of_volumeGrowth_zero_existence hgrowth hex

#print axioms manyGoodAnnuliStmt_of_volumeGrowth_zero_existence
#print axioms manyVeryGoodAnnuliStmt_of_volumeGrowth_zero_existence
#print axioms harnackTypeComponentStmt_of_volumeGrowth_zero_existence
#print axioms harnackTypeEstimateStmt_of_volumeGrowth_zero_existence

end HarmonicBalls.Section6
