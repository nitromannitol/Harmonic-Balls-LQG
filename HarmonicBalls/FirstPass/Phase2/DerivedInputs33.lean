import HarmonicBalls.FirstPass.Phase2.DerivedInputs19
import HarmonicBalls.FirstPass.Phase2.DerivedInputs23
import HarmonicBalls.FirstPass.Phase2.RootedDominationCanonical

/-! # Counted wrappers with the row-8 input traded (fp-phase2-di33-row8-trade)

Ledger row 8 is `LocalRootedFieldMeasureDomination` (FirstPass/Frozen/S8c.lean:55). The counted
declarations below bind it as a hypothesis `hL1`. Each wrapper has the same conclusion as its
counted declaration, drops `hL1`, and takes instead the Lemma A.10 input `hSub`
(`DMSLemmaA10WholePlaneMarkedSub`, FirstPass/Frozen/S11i.lean:57). The row-8 input is then
`localRootedFieldMeasureDomination_of_sub hSub` (RootedDominationCanonical.lean).

The binder count of each wrapper equals that of its counted declaration (`hL1` replaced by `hSub`).
None of the four counted declarations binds ledger row 17 or row 23, so no wrapper of
DerivedInputs32 is needed. -/

universe u

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls.Closure

/-- Lemma 5.2 (`ClusterContinuityStmt`) from `closure_5_2_derivedInputs19` with row 8 traded for `hSub`. -/
theorem closure_5_2_derivedInputs33
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hSub : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : ClusterContinuityStmt.{u} :=
  closure_5_2_derivedInputs19 hDG hCC hE (localRootedFieldMeasureDomination_of_sub hSub) hE3

/-- Proposition 11.6 (`AnnulusMassBoundByHarmonicChainStmt`) from `closure_11_6_derivedInputs19`
with row 8 traded for `hSub`. -/
theorem closure_11_6_derivedInputs33
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hSub : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : AnnulusMassBoundByHarmonicChainStmt.{u} :=
  closure_11_6_derivedInputs19 hDG hCC hE (localRootedFieldMeasureDomination_of_sub hSub) hE3

/-- Corrected Theorem 9.2 (`SubharmonicBallUniquenessC51Stmt`, S9c.lean:41) from
`closure_9_2_derivedInputs19` with row 8 traded for `hSub`. -/
theorem closure_9_2_derivedInputs33
    (hSub : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    : HarmonicBalls.S9c.SubharmonicBallUniquenessC51Stmt.{u} :=
  closure_9_2_derivedInputs19 (localRootedFieldMeasureDomination_of_sub hSub) hE3 hDG hCC hE

end HarmonicBalls.Closure

namespace HarmonicBalls

/-- Proposition 8.2 (`TypicalPointManyGoodScalesStmt`) from `firstPass_8_2_S8d_noWeyl_derivedInputs23`
with row 8 traded for `hSub`. -/
theorem firstPass_8_2_S8d_noWeyl_derivedInputs33
    (hSub : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hEx : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : TypicalPointManyGoodScalesStmt.{u} :=
  firstPass_8_2_S8d_noWeyl_derivedInputs23 (localRootedFieldMeasureDomination_of_sub hSub) hDG hEx hCC hE3

end HarmonicBalls
