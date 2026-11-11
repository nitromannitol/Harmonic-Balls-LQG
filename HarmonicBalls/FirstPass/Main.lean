import HarmonicBalls.Proposed.LQG
import HarmonicBalls.FirstPass.S1S10
import HarmonicBalls.FirstPass.S2S3S4S9SA
import HarmonicBalls.FirstPass.S5S7S8
import HarmonicBalls.FirstPass.S6
import HarmonicBalls.FirstPass.S11
import HarmonicBalls.FirstPass.Frozen.S1S10

/-!
# main theorems

Composition of the committed `firstPass_<sec>_<num>` theorems into one theorem per main result
(Theorem 1.1, Theorem 1.2, Proposition 1.3). Each `firstPassMain_<sec>_<num>` has as hypotheses only:
* EXTERNAL Props: the staged literature inputs of `Proposed/LQG.lean` (pending source-check),
  the cited input I2 `LQGVolumeGrowthAllScalesStmt`, the FROZEN `TorhorstSimpleLoopFrozen`;
* the Draft statements of the numbered results not yet PROVED-FP: `TypicalPointManyGoodScalesStmt` (Lemma 8.2),
  `ManyConeBadScalesStmt` (Lemma 11.7), `ManyPinchScalesStmt` (Lemma 11.13).

Every other Draft hypothesis of the printed proofs is discharged by a `firstPass_` theorem. Literature inputs of
the Section 2, 3, 4, 9 and A files are taken at the arguments they use: the `α₀ = 0` instances are specialisations
of the `∀ α₀` form (`hCC`, `hE`) taken as the hypothesis, so no new Prop is introduced.

-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Theorem 1.1 (theorem:harmonic-balls): existence and uniqueness of the family of harmonic balls.
Composition of `firstPass_1_1` with `firstPass_5_5` (Theorem 5.5) and `firstPass_5_6` (Proposition 5.6). -/
theorem firstPassMain_1_1
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hTyp : TypicalPointManyGoodScalesStmt.{u}) :
    ExistenceUniquenessHarmonicBallsStmt.{u} := by
  have hCC0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc :=
    fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc
  have hCCi : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc :=
    fun {Ω} _ P γ α₀ hC hcirc => hCC Ω P γ α₀ hC hcirc
  have h55 := firstPass_5_5 hDG hCCi hE hTyp
  have h56 := firstPass_5_6 hDG hCC0 hE
  exact firstPass_1_1 h55 h56

/-- Theorem 1.2 (theorem:harmonic-balls-properties): novelty of the harmonic balls, i.e. the Jordan
clause (Proposition 10.7), the non-Lipschitz clause (Proposition 11.2) and the non-metric-ball clause (Proposition
11.11), with the family of Theorem 1.1. Open Draft hypotheses: `h7` (Lemma 11.7), `h13` (Lemma 11.13), `hTyp` (Lemma 8.2). -/
theorem firstPassMain_1_2
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hTyp : TypicalPointManyGoodScalesStmt.{u})
    (h7 : ManyConeBadScalesStmt.{u})
    (h13 : ManyPinchScalesStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    (hmetricAxioms : ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    HarmonicBallNoveltyStmt.{u} := by
  have hCC0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc :=
    fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc
  have hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc :=
    fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc
  have hCCi : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc :=
    fun {Ω} _ P γ α₀ hC hcirc => hCC Ω P γ α₀ hC hcirc
  have h55 := firstPass_5_5 hDG hCCi hE hTyp
  have h56 := firstPass_5_6 hDG hCC0 hE
  -- Proposition 10.7 (Jordan clause)
  have h32 := firstPass_3_2 hDG hAff hCC0 hW hE0 hN
  have h10 := firstPass_10_6 (firstPass_10_1 hI2 hE0) h32 hTor
  have hjordan := firstPass_10_7 hI2 h55 h10 hAff hCC
  -- Proposition 11.2 (non-Lipschitz) and Proposition 11.11 (non-metric-ball)
  have h68 := FirstPass.S6.firstPass_6_8 hDG hCC0 hE
  have h610 := FirstPass.S6.firstPass_6_10 hDG hCC0 hE
  have h8 := firstPass_8_1 hDG hCC0 hE hTyp
  have h6 := firstPass_11_6 hI2 h68 h610 h8 h55 hAff hCC
  have hlip := firstPass_11_2 (firstPass_11_5 h6 h7 hI2)
  have hmetric := firstPass_11_11 h6 h13 hI2 hmetricAxioms
  exact firstPass_1_2 h55 h56 hjordan hlip hmetric

/-- Proposition 1.3 (prop:locally-determined): closed harmonic balls are local sets for the field.
Composition of `firstPass_1_3` with `firstPass_5_5` and `firstPass_5_6`. -/
theorem firstPassMain_1_3
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hTyp : TypicalPointManyGoodScalesStmt.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureLocality P γ α₀ hC hcirc) :
    HarmonicBallLocalSetStmt.{u} := by
  have hCC0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc :=
    fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc
  have hCCi : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc :=
    fun {Ω} _ P γ α₀ hC hcirc => hCC Ω P γ α₀ hC hcirc
  have h55 := firstPass_5_5 hDG hCCi hE hTyp
  have h56 := firstPass_5_6 hDG hCC0 hE
  exact firstPass_1_3 hI2 h55 h56 hmeasure


end HarmonicBalls
