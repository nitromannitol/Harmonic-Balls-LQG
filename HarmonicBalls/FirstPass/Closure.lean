import HarmonicBalls.FirstPass.Main
import HarmonicBalls.FirstPass.Closure.Sec6
import HarmonicBalls.FirstPass.Closure.SecA45
import HarmonicBalls.FirstPass.Closure.Sec78910
import HarmonicBalls.FirstPass.Closure.Sec11

/-!
# Closure of the main theorems of Section 1 (fp-closure-11-and-main, owner z11)

Each `closure_1_k` concludes exactly the conclusion of `firstPassMain_1_k` (`FirstPass/Main.lean`), with its
paper-owned hypotheses discharged by the closure theorems of `FirstPass/Closure/*.lean`:

| result | closure | remaining hypotheses (class) | OPEN items |
|---|---|---|---|
| Theorem 1.1 (`ExistenceUniquenessHarmonicBallsStmt`) | `closure_1_1` | hDG, hCC, hE, hAff, hW, hN (Proposed); hL1, hWeyl, hE1, hE3, hB (FROZEN or cited inputs of 8.2) | none |
| Theorem 1.2 (`HarmonicBallNoveltyStmt`) | `closure_1_2` | hDG, hAff, hCC, hW, hE, hN, hI2, hmetricAxioms (Proposed or external); hTor (FROZEN); hL1, hWeyl, hE1, hE3, hB; hCamp, hDecFrozen, hDec, hCM (FROZEN, of 11.7) | h13 = printed Lemma 11.13 (`ManyPinchScalesStmt`); hI2 (see the notes of this task) |
| Proposition 1.3 (`HarmonicBallLocalSetStmt`) | `closure_1_3` | hI2, hDG, hCC, hE, hmeasure, hAff, hW, hN (external); hL1, hWeyl, hE1, hE3, hB | hI2 (see the notes of this task) |

Paper-owned hypotheses discharged: `TypicalPointManyGoodScalesStmt` (Lemma 8.2) by `closure_8_2`
(`FirstPass/Closure/Sec78910.lean`); `ManyConeBadScalesStmt` (Lemma 11.7) by `closure_11_7` (`FirstPass/Closure/Sec11.lean`).
Not discharged: `ManyPinchScalesStmt` (Lemma 11.13, printed form; only the corrected form is proved) and
`LQGVolumeGrowthAllScalesStmt` (input I2), both kept as hypotheses and marked OPEN.
No cycle: the closures of Section 1 use only the closures of Sections 6 to 11, which do not use Section 1.
-/

namespace HarmonicBalls.Closure

open MeasureTheory

universe u

/-- **Closure of Theorem 1.1** (`ExistenceUniquenessHarmonicBallsStmt`, `firstPassMain_1_1`). The paper-owned hypothesis
`TypicalPointManyGoodScalesStmt` (Lemma 8.2) is discharged by `closure_8_2`. -/
theorem closure_1_1
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u}) (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u}) (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0}) :
    ExistenceUniquenessHarmonicBallsStmt.{u} :=
  firstPassMain_1_1 hDG hCC hE (closure_8_2 hL1 hWeyl hE1 hE3 hB hDG hAff hCC hW hE hN)

/-- **Closure of Theorem 1.2** (`HarmonicBallNoveltyStmt`, `firstPassMain_1_2`). Paper-owned hypotheses:
`TypicalPointManyGoodScalesStmt` (Lemma 8.2, `closure_8_2`) and `ManyConeBadScalesStmt` (Lemma 11.7, `closure_11_7`).
**OPEN**: `ManyPinchScalesStmt` (h13, printed Lemma 11.13), kept as a hypothesis (only the corrected form is proved). -/
theorem closure_1_2
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h13 : ManyPinchScalesStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    (hmetricAxioms : ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u}) (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u}) (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u}) :
    HarmonicBallNoveltyStmt.{u} :=
  firstPassMain_1_2 hDG hAff hCC hW hE hN hI2
    (closure_8_2 hL1 hWeyl hE1 hE3 hB hDG hAff hCC hW hE hN)
    (closure_11_7 hDG hCamp hDecFrozen hDec hCM
      (fun γ α₀ Ω _ P hC hcirc => hCC Ω P γ α₀ hC hcirc)
      (fun γ α₀ Ω _ P hC hcirc => hE Ω P γ α₀ hC hcirc)
      (fun γ α₀ Ω _ P hC hcirc => hN Ω P γ α₀ hC hcirc))
    h13 hTor hmetricAxioms

/-- **Closure of Proposition 1.3** (`HarmonicBallLocalSetStmt`, `firstPassMain_1_3`). The paper-owned hypothesis
`TypicalPointManyGoodScalesStmt` (Lemma 8.2) is discharged by `closure_8_2`. -/
theorem closure_1_3
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureLocality P γ α₀ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u}) (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u}) (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0}) :
    HarmonicBallLocalSetStmt.{u} :=
  firstPassMain_1_3 hI2 hDG hCC hE (closure_8_2 hL1 hWeyl hE1 hE3 hB hDG hAff hCC hW hE hN) hmeasure

end HarmonicBalls.Closure
