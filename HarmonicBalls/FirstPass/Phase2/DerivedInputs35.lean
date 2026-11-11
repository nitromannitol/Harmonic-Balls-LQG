import HarmonicBalls.FirstPass.Phase2.DerivedInputs34
import HarmonicBalls.FirstPass.Closure.Sec78910
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling

/-! # Counted wrappers with the row-5 input traded (fp-phase2-di35-derived-sweep)

Ledger row 5 is `LQGMeasureWeylScaling` (Proposed/LQG.lean:107), a literature input in universal form.
The derived theorem `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124)
supplies it without any further hypothesis.

Counted declarations of COUNTED-MANIFEST.md whose signature binds row 5 (grepped at this round):
- result 8.3, `closure_8_3` (FirstPass/Closure/Sec78910.lean:150), binder `hW`;
- result 11.16, `firstPass_11_16_corrected_derivedInputs34` (FirstPass/Phase2/DerivedInputs34.lean:35), binder `hWeyl`.

No counted declaration binds ledger rows 11, 26, 29, 37 or 42 (LocalLQGInsertionWeylOffOrigin,
WeylInternalClosedFrozen, WholePlaneGFFExistsFrozen, CameronMartinGFFReweighting,
LQGMetricLengthUnivFrozen), so no wrapper is written for them in this file.

Each wrapper has the same conclusion as its counted declaration and drops the row-5 binder; the
binder count is strictly lower. -/

universe u

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls.Closure

/-- Result 8.3 (`OriginManyGoodScalesStmt`) from the counted declaration `closure_8_3`
(Sec78910.lean:150) with the row-5 binder `hW` dropped; `hW` is supplied by the binder-free
`HarmonicBalls.Section6.lqgMeasureWeylScaling` at `α₀ = 0`. -/
theorem closure_8_3_derivedInputs35
    (hholder : GreenPotentialHolderStmt.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    : OriginManyGoodScalesStmt.{u} :=
  closure_8_3 hholder hDG hN hCC hE
    (fun Ω _ P γ hC hcirc => HarmonicBalls.Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc)

end HarmonicBalls.Closure

namespace HarmonicBalls

/-- Result 11.16 (`PinchSecondEventFaithfulStmt`) from the counted declaration
`firstPass_11_16_corrected_derivedInputs34` (FirstPass/Phase2/DerivedInputs34.lean:35) with the
row-5 binder `hWeyl` dropped; `hWeyl` is supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling`
at `α₀ = 0`. The other binders are those of the DerivedInputs34 wrapper, unchanged. -/
theorem firstPass_11_16_corrected_derivedInputs35
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hEx : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hNa0 : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ 0 hC hcirc)
    (hNa : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hPos : PinchFirstEventFaithfulStmt.{u}) (hD : SmallMetricDiameterLargeMassStmt.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u}) :
    PinchSecondEventFaithfulStmt.{u} :=
  firstPass_11_16_corrected_derivedInputs34 hAx hholder hEx
    (fun γ Ω _ P hC hcirc => HarmonicBalls.Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc)
    hNa0 hNa hPos hD hMk

end HarmonicBalls
