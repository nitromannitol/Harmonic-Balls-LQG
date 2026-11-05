import HarmonicBalls.Proofs.Sec8.TypicalPointStatement
import HarmonicBalls.Proofs.Sec9.LQGExistenceConsequences
import HarmonicBalls.Proofs.Sec6.SevenAdicFineSupportPrevalence

/-! # Weak uniqueness from rooted measure-law comparisons

The mass-bound, coordinate-change and LQG-existence hypotheses are staged
literature inputs pending source review. The rooted and recentered law
comparisons are a separate proof obligation, not a literature input. The
Section 6 dependency chain awaits campaign audit.
-/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

universe u

section

variable
  (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureCoordChange P γ α hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureExistence P γ α hC hcirc)
    (hcomparison : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
      (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ ν : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
      (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ),
      0 < γ → γ < 2 → α₀ < lqgQ γ → IsLQGMeasureOfField P γ γ hcirc ν →
      ∃ S : Measure Ω, P ≪ S ∧ AEMeasurable μ S ∧
        (∀ᵐ ω ∂S, IsLocallyFiniteMeasure (μ ω)) ∧
      ∃ (w : ℂ → ℝ≥0∞) (hw : Measurable w),
        (∀ z, w z ≠ 0) ∧ (∀ z, w z ≠ ∞) ∧
      ∃ ρ : ℕ → Measure ℂ, (∀ n, ρ n ≪ volume) ∧
      ∃ shift : ℕ → ℂ × Ω → Ω, (∀ n, Measurable (shift n)) ∧
      ∃ R : ℕ → ℂ → Measure Ω,
        (∀ n, P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ
          (hGFF.aemeasurable_lqgMeasure hμ) (weightedLocalization w n)
          (measurableSet_weightedLocalization hw n) w hw) ≪
            shiftedRootReferenceLaw (ρ n) P (shift n)) ∧
        (∀ n, ∀ᵐ z ∂ρ n, P.map (fun ω => shift n (z, ω)) ≪ R n z) ∧
        (∀ n, ∀ᵐ z ∂ρ n, R n z ≪ S) ∧
        (∀ n, ∀ᵐ z ∂ρ n,
          (R n z).map (fun ω => (μ ω).map (fun v : ℂ => v - z)) ≪ P.map ν))

include hDG hCC hE hcomparison

/-- The typical-point estimate follows from three staged LQG inputs and the
explicit rooted and recentered measure-law comparisons. -/
theorem typicalPointManyGoodScalesStmt_of_staged_inputs_and_comparison :
    TypicalPointManyGoodScalesStmt.{u} := by
  have hCC0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc :=
    fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc
  have hI2 := lqgVolumeGrowthAllScalesStmt_of_existence hDG hCC0 hE
  exact typicalPointManyGoodScalesStmt_of_ambientLaw hI2
    (lqgMeasureFullSupportStmt_of_existence hDG hCC0 hE)
    (Section6.goodAnnuliSubRangeStep_of_volumeGrowth_fineSupport hI2) hE
    (fun Ω _ P γ hC hcirc => Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc)
    (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc)
    hCC hcomparison

/-- The corrected weak Proposition 9.2 follows under the same staged inputs
and explicit comparisons. -/
theorem subharmonicBallUniquenessWeak_of_staged_inputs_and_comparison :
    SubharmonicBallUniquenessWeakStmt.{u} := by
  apply subharmonicBallUniquenessWeak_of_volumeGrowth_typicalScales
    (lqgVolumeGrowthAllScalesStmt_of_existence hDG
      (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE)
  exact typicalPointManyGoodScalesStmt_of_staged_inputs_and_comparison hDG hCC hE hcomparison

end

end HarmonicBalls
