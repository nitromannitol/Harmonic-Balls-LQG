import HarmonicBalls.FirstPass.S5S7S8
import HarmonicBalls.FirstPass.S6
import HarmonicBalls.FirstPass.S8d
import HarmonicBalls.FirstPass.S9c
import HarmonicBalls.FirstPass.S2S3S4S9SA
import HarmonicBalls.FirstPass.S1S10
import HarmonicBalls.FirstPass.S1S10.CrossingLemma

/-!
# Closure of the counted numbered results of Sections 7-10

For each counted result `X.Y` of Sections 7-10 (paper-owned in `docs/campaign/INVENTORY.tsv`), a theorem
`HarmonicBalls.Closure.closure_X_Y` with the conclusion of the counted `firstPass_X_Y` (corrected form where
counted). Its hypotheses are only:
* Proposed literature inputs (`HarmonicBalls/Proposed/LQG.lean`: `WholePlaneLQGBallMassBounds`,
  `LQGMeasureCoordChange`, `LQGMeasureExistence`, `LQGMeasureWeylScaling`, `LQGMeasureNonatomic`,
  `WholePlaneGFFAffineInvariance`), in the universal (`∀ α₀`, `∀ α`) forms of `Main.lean`;
* FROZEN Props (`FirstPass/Frozen/*.lean`): `LocalRootedFieldMeasureDomination`,
  `LocalLQGInsertionWeylOffOrigin`, `LQGMeasureOfProfileMeasurableFrozen`, `PhaseTorusDoublingProductErgodicFrozen`,
  `BirkhoffPointwiseErgodic`, `TorhorstSimpleLoopFrozen`;
* the cited input `GreenPotentialHolderStmt` (HB Proposition 2.5, `hholder`, used by Lemma 8.3 only).

Every other paper-owned hypothesis is discharged by its `firstPass_*` theorem, applied directly (the same
binders as the counted theorem), recursively:
* Lemma 8.2 (`TypicalPointManyGoodScalesStmt`, `firstPass_8_2`, `FirstPass/S8d.lean`) is the hub of the chain;
  its own hypothesis `VeryGoodAnnulusProbabilityStmt` (Lemma 6.7) is `firstPass_6_7` (`FirstPass/S6.lean`);
  its full-support input `LQGMeasureFullSupportStmt` (unnumbered consequence, Draft Section 2) is
  `lqgMeasureFullSupportStmt_of_literature` from the Proposed inputs.
* Theorem 5.5 (`ExistenceHarmonicBallsStmt`, `firstPass_5_5`) for Proposition 10.7.
* The volume-growth input `LQGVolumeGrowthAllScalesStmt` (I2) is `lqgVolumeGrowthAllScalesStmt_of_five_staged_inputs`
  from the Proposed inputs.
* Lemma 3.2 (`ClusterOpenLaplacianStmt`, `firstPass_3_2`) for Proposition 10.6.
* Lemma 10.1 (`ClusterBoundedCrossingsStmt`, `firstPass_10_1`) for Proposition 10.6.
* Lemma 10.5 (`firstPass_10_5_corrected`, [C48]) is the deterministic statement used by Proposition 10.6; its
  premises on `G` (`hEcross`) are the quantifiers of the counted theorem, not paper-owned Props.

Not closed here: Lemma 9.1 (`ObstacleComparisonStmt`) is cited (Shahgholian-Sjödin 2013, Sakai 1984), not a paper-owned
numbered result, so it has no closure.
-/

open MeasureTheory

namespace HarmonicBalls.Closure

universe u

/-! ## Lemma 8.2: the hub of Sections 7-9 -/

/-- Lemma 8.2 (lemma:mu_h-doubling-and-harnack, line 2151), closure of `firstPass_8_2`. Its hypotheses are the
FROZEN Props `LocalRootedFieldMeasureDomination` (`hL1`), `LocalLQGInsertionWeylOffOrigin` (`hWeyl`),
`LQGMeasureOfProfileMeasurableFrozen` (`hE1`), `PhaseTorusDoublingProductErgodicFrozen` (`hE3`) and
`BirkhoffPointwiseErgodic` (`hB`), and the Proposed inputs `hDG`, `hAff`, `hCC`, `hW`, `hE`, `hN`. -/
theorem closure_8_2
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
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
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    TypicalPointManyGoodScalesStmt.{u} := by
  have hCC0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc :=
    fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc
  have hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc :=
    fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc
  have hfull : LQGMeasureFullSupportStmt.{u} :=
    HarmonicBalls.lqgMeasureFullSupportStmt_of_literature hDG hAff hCC0 hW hE0 hN
  have hL67 : VeryGoodAnnulusProbabilityStmt.{u} :=
    HarmonicBalls.FirstPass.S6.firstPass_6_7 hDG hCC0 hE
  exact HarmonicBalls.firstPass_8_2 hL1 hfull hWeyl hL67 hE hN hAff hCC hE1 hE3 hB

/-! ## Section 7 -/

/-- Proposition 7.1 (prop:upper-bound-polynomially-high-prob, line 1956), closure of `firstPass_7_1`. Hypotheses:
the Proposed inputs `hDG`, `hCC`, `hE` only. -/
theorem closure_7_1
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc) :
    ClusterUpperBoundPolyHighProbStmt.{u} :=
  HarmonicBalls.firstPass_7_1 hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE

/-- Proposition 7.2 (prop:continuity-of-clusters, line 2021), closure of `firstPass_7_2`. Its hypothesis `hTyp`
(Lemma 8.2) is `closure_8_2`; the remaining hypotheses are the Proposed and FROZEN inputs of `closure_8_2`. -/
theorem closure_7_2
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
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
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    ClusterTimeContinuityStmt.{u} :=
  HarmonicBalls.firstPass_7_2 hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE
    (closure_8_2 hL1 hWeyl hE1 hE3 hB hDG hAff hCC hW hE hN)

/-! ## Section 8 -/

/-- Proposition 8.1 (prop:boundary-measure-zero, line 2122), closure of `firstPass_8_1`. Its hypothesis `hTyp`
(Lemma 8.2) is `closure_8_2`. -/
theorem closure_8_1
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
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
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    BoundaryMeasureZeroOfCompactClusterStmt.{u} :=
  HarmonicBalls.firstPass_8_1 hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE
    (closure_8_2 hL1 hWeyl hE1 hE3 hB hDG hAff hCC hW hE hN)

/-- Lemma 8.3 (lemma:doubling-alpha, line 2160), closure of `firstPass_8_3`. Hypotheses: the cited input `hholder`
(`GreenPotentialHolderStmt`, HB Proposition 2.5, proved in the paper by citation to Ponce §16.2) and the Proposed inputs. -/
theorem closure_8_3
    (hholder : GreenPotentialHolderStmt.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc) :
    OriginManyGoodScalesStmt.{u} :=
  HarmonicBalls.firstPass_8_3 hholder hDG hN hCC
    (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc) hW

/-! ## Section 9 -/

/-- Proposition 9.2 (prop:sub-harmonic-ball-uniqueness), corrected form [C51], closure of
`HarmonicBalls.S9c.firstPass_9_2_corrected`. Its hypothesis `h82` (Lemma 8.2) is `closure_8_2`. -/
theorem closure_9_2
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
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
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    HarmonicBalls.S9c.SubharmonicBallUniquenessC51Stmt.{u} :=
  HarmonicBalls.S9c.firstPass_9_2_corrected hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hW
    (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc) hN
    (closure_8_2 hL1 hWeyl hE1 hE3 hB hDG hAff hCC hW hE hN)

/-- Lemma 9.3 (lemma:contains-boundary), closure of `firstPass_9_3`. Hypotheses: the Proposed inputs only. -/
theorem closure_9_3
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
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    HarmonicBallBoundarySubsetStmt.{u} :=
  HarmonicBalls.firstPass_9_3 hDG hAff (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc)
    hW (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc) hN

/-- Lemma 9.4 (lemma:regular-open-ae), closure of `firstPass_9_4`. Hypotheses: the Proposed inputs only. -/
theorem closure_9_4
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
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    RegularOpenEqOfAEEqStmt.{u} :=
  HarmonicBalls.firstPass_9_4 hDG hAff (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc)
    hW (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc) hN

/-! ## Section 10 -/

/-- Lemma 10.1 (lemma:cannot-cross), closure of `firstPass_10_1`. Its volume-growth input `LQGVolumeGrowthAllScalesStmt`
(I2) is `lqgVolumeGrowthAllScalesStmt_of_five_staged_inputs`, from the Proposed inputs. -/
theorem closure_10_1
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    ClusterBoundedCrossingsStmt.{u} :=
  HarmonicBalls.firstPass_10_1
    (HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_five_staged_inputs hDG
      (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hW (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc) hN)
    (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc)

/-- Lemma 10.5 (lemma:crossing-connected), corrected form [C48], closure of `firstPass_10_5_corrected`. The conclusion
is the deterministic statement for a set `G`; `hEcross` (finitely many small crossing components off a finite set) is
a premise of the counted theorem, not a paper-owned Prop: for the clusters it is supplied by Lemma 10.1 in
`closure_10_6`. The only other hypothesis is the FROZEN `TorhorstSimpleLoopFrozen`. -/
theorem closure_10_5 {G : Set ℂ} (hGne : G.Nonempty) (hGb : Bornology.IsBounded G)
    (hGo : IsOpen G) (hGc : IsConnected G)
    (hEcross : ∃ E : Set ℂ, E.Finite ∧ ∀ p ∈ frontier G \ E, ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < δ ∧
      (crossingComponents (G ∩ Metric.ball p (2 * r)) p (r / 3) (2 * r)).Finite)
    (hTor : TorhorstSimpleLoopFrozen) :
    IsLocallyConnectedSet (closure G) ∧ (∀ a : ℂ, ¬ IsCutPoint (closure G) a) ∧
      ∀ C ∈ connectedComponentsIn (closure G)ᶜ, IsSimpleLoop (frontier C) :=
  HarmonicBalls.firstPass_10_5_corrected hGne hGb hGo hGc hEcross hTor

/-- Proposition 10.6 (prop:boundary-simple-loop), corrected form [C49], closure of `firstPass_10_6`. Its hypotheses
`h10` (Lemma 10.1) and `h32` (Lemma 3.2, `ClusterOpenLaplacianStmt`) are `closure_10_1` and `firstPass_3_2`. -/
theorem closure_10_6
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
    (hTor : TorhorstSimpleLoopFrozen) :
    ComplementComponentBoundarySimpleLoopStmt.{u} :=
  HarmonicBalls.firstPass_10_6 (closure_10_1 hDG hCC hW hE hN)
    (HarmonicBalls.firstPass_3_2 hDG hAff (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc)
      hW (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc) hN)
    hTor

/-- Proposition 10.7 (prop:boundary-simple-loop-full-cluster), corrected as [C50], closure of `firstPass_10_7`.
Its hypotheses: `h55` (Theorem 5.5, `firstPass_5_5`, which takes Lemma 8.2 = `closure_8_2`), `h10` (`closure_10_6`),
the volume-growth input (`lqgVolumeGrowthAllScalesStmt_of_five_staged_inputs`), and the Proposed and FROZEN
inputs listed in `closure_8_2`, `closure_10_6`. -/
theorem closure_10_7
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
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
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallComplementBoundaryJordanStmt.{u} :=
  HarmonicBalls.firstPass_10_7
    (HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_five_staged_inputs hDG
      (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hW (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc) hN)
    (HarmonicBalls.firstPass_5_5 hDG (fun {Ω} _ P γ α₀ hC hcirc => hCC Ω P γ α₀ hC hcirc) hE
      (closure_8_2 hL1 hWeyl hE1 hE3 hB hDG hAff hCC hW hE hN))
    (closure_10_6 hDG hAff hCC hW hE hN hTor) hAff hCC

end HarmonicBalls.Closure

