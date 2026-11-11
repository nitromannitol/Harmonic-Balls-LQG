import HarmonicBalls.FirstPass.Closure.Faithful12
import HarmonicBalls.FirstPass.Closure.Bridge12Canonical
import HarmonicBalls.FirstPass.Canonical.Stmts
import HarmonicBalls.FirstPass.Canonical.Novelty
import HarmonicBalls.FirstPass.Canonical.NotMetricBall
import HarmonicBalls.FirstPass.S8c.WeylOffOriginDerived

/-!
# Theorem 1.2 at the canonical Weyl exponent, without `hWeyl`

File `HarmonicBalls/FirstPass/Closure/Main12Canonical.lean`. Closure chain of Theorem 1.2
(`HarmonicBallNoveltyStmt`, `Draft/Section1.lean:124`) at the canonical exponent `ξ = lqgXi γ` (`FirstPass/S11i/Faithful.lean:94`), with the model quantified before the density (Correction 3,
`ManyPinchScalesCanonicalModelStmt`, `Closure/Bridge12Canonical.lean:42`).

Declarations: `firstPassMain_1_2_canonical` (`FirstPass/Main.lean:55`), `closure_1_2_canonical` (`FirstPass/Closure.lean:183`),
`harmonicBallNoveltyFaithful_of_canonical`, and `closure_1_2_faithful_canonical` (`FirstPass/Closure/Faithful12.lean:64`).
Each is a copy of its original with the substitutions listed in the docstrings. No new mathematics.
-/

universe u

namespace HarmonicBalls

section FirstPassMain

open MeasureTheory Metric Set Filter Topology

/-- Theorem 1.2 at the canonical exponent `ξ = lqgXi γ`. Copy of `firstPassMain_1_2`
(`FirstPass/Main.lean:55-103`) with `h13 : ManyPinchScalesStmt` replaced by `h13 : ManyPinchScalesCanonicalModelStmt`
 (model quantified before the density), `firstPass_11_11` by `firstPass_11_11_canonical`, and
`firstPass_1_2` by `firstPass_1_2_canonical`. All other hypotheses are unchanged. -/
theorem firstPassMain_1_2_canonical
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
    (h13 : HarmonicBalls.Closure.ManyPinchScalesCanonicalModelStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    (hmetricAxioms : ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    HarmonicBallNoveltyCanonicalStmt.{u} := by
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
  -- Proposition 11.2 (non-Lipschitz) and Proposition 11.11 (non-metric-ball, canonical exponent)
  have h68 := FirstPass.S6.firstPass_6_8 hDG hCC0 hE
  have h610 := FirstPass.S6.firstPass_6_10 hDG hCC0 hE
  have h8 := firstPass_8_1 hDG hCC0 hE hTyp
  have h6 := firstPass_11_6 hI2 h68 h610 h8 h55 hAff hCC
  have hlip := firstPass_11_2 (firstPass_11_5 h6 h7 hI2)
  have hmetric := firstPass_11_11_canonical h6 h13 hI2 hmetricAxioms
  exact firstPass_1_2_canonical h55 h56 hjordan hlip hmetric

end FirstPassMain

namespace Closure

/-- **Closure of Theorem 1.2 at the canonical exponent** (`HarmonicBallNoveltyCanonicalStmt`). Copy of `closure_1_2`
(`FirstPass/Closure.lean:183-219`) with:
* the binder `hWeyl` removed; the Weyl input off the origin is `localLQGInsertionWeylOffOrigin_derived`
  (`FirstPass/S8c/WeylOffOriginDerived.lean:88`);
* the binder `hStep8 : Step8IdentificationStmt` replaced by `hId : Step8IdentityGivenPinchEventCanonicalStmt`, the open part (d)
  of Lemma 11.13 at the canonical exponent, which is the only open input of `closure_11_13_canonical` (`Closure/Sec11.lean:400`);
  the other inputs of `closure_11_13_canonical` are binders here, with the same names, except:
  `hLoc` is `hDec` (the same proposition `LocalLQGDecoderCommonFrozen`), and its `hW : WeylInternalClosedFrozen` is `hWIC`
  (`hW` is the binder `LQGMeasureWeylScaling` of `closure_1_2`);
* the coordinate-change input of `closure_11_13_canonical`, which is stated at `α₀ = 0`, is `hCC` at `α₀ = 0`;
* the density of `ManyPinchScalesCanonicalModelStmt` obtained by `manyPinchScalesCanonicalModel_of_canonical`
  (`Closure/Bridge12Canonical.lean:54`) from `closure_11_13_canonical`. -/
theorem closure_1_2_canonical
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hLen : LQGMetricLengthUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hμW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hmass : LQGMassFunctionalMeasurableFrozen.{u})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{u})
    (hCMRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hMassM : LQGMeasureSquareMeasurableFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hWIC : WeylInternalClosedFrozen)
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallNoveltyCanonicalStmt.{u} :=
  firstPassMain_1_2_canonical hDG hAff hCC hW hE hN (volumeGrowthI2_of_staged hDG hCC hW hE hN)
    (closure_8_2 hL1 localLQGInsertionWeylOffOrigin_derived.{u} hE1 hE3 hB hDG hAff hCC hW hE hN)
    (closure_11_7 hDG hCamp hDecFrozen hDec hCM
      (fun γ α₀ Ω _ P hC hcirc => hCC Ω P γ α₀ hC hcirc)
      (fun γ α₀ Ω _ P hC hcirc => hE Ω P γ α₀ hC hcirc)
      (fun γ α₀ Ω _ P hC hcirc => hN Ω P γ α₀ hC hcirc))
    (manyPinchScalesCanonicalModel_of_canonical
      (closure_11_13_canonical (hAx := hAx) (hLen := hLen) (hN2 := hN2) (hμW := hμW) (hLoc := hDec)
        (hCanon := hCanon) (hNonat := hNonat) (hExists := hExists) (hDG := hDG)
        (hCC := fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) (hE := hE) (hfr := hfr) (hmass := hmass)
        (hCMAbs := hCMAbs) (hCMRew := hCMRew) (hComp := hComp) (hMf := hMf) (hDiam := hDiam) (hMk := hMk)
        (hholder := hholder) (hShift := hShift) (hFD := hFD) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10)
        (hMassM := hMassM) (hSupM := hSupM) (hFin := hFin) (hW := hWIC) (hM1 := hM1) (hM2 := hM2) (hId := hId)))
    hTor
    (fun γ α₀ ξ _ _ _ Ω _ P hC hcirc _ => hAx Ω P γ ξ α₀ hC hcirc)

/-- Restriction of `HarmonicBallNoveltyCanonicalStmt` to the radii `0 < s`, giving `HarmonicBallNoveltyFaithfulStmt`
(`Closure/Faithful12.lean:39`). Since `lqgXi γ = γ / lqgGraphDimension γ` (`FirstPass/S11i/Faithful.lean:94`), the metric
clause of the two statements is the same at `ξ`; only the radius restriction is added. Mirror of
`harmonicBallNoveltyFaithful_of_stmt` (`Closure/Faithful12.lean:52`). -/
theorem harmonicBallNoveltyFaithful_of_canonical (h : HarmonicBallNoveltyCanonicalStmt.{u}) :
    HarmonicBallNoveltyFaithfulStmt.{u} := by
  intro γ α₀ hγ0 hγ2 hα Ω inst P hC hcirc μ hW hμ Λ hΛ
  obtain ⟨hA, hB⟩ := h γ α₀ hγ0 hγ2 hα Ω P hC hcirc μ hW hμ Λ hΛ
  refine ⟨hA, fun D hD => ?_⟩
  filter_upwards [hB D hD] with ω hω
  filter_upwards [hω] with t ht
  intro ht0 w s _
  exact ht ht0 w s

/-- **Closure of the faithful Theorem 1.2 at the canonical exponent** (`HarmonicBallNoveltyFaithfulStmt`): the hypotheses of
`closure_1_2_canonical`, with the conclusion restricted by `harmonicBallNoveltyFaithful_of_canonical`. Mirror of
`closure_1_2_faithful` (`Closure/Faithful12.lean:64`). -/
theorem closure_1_2_faithful_canonical
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hLen : LQGMetricLengthUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hμW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hmass : LQGMassFunctionalMeasurableFrozen.{u})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{u})
    (hCMRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hMassM : LQGMeasureSquareMeasurableFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hWIC : WeylInternalClosedFrozen)
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallNoveltyFaithfulStmt.{u} :=
  harmonicBallNoveltyFaithful_of_canonical.{u}
    (closure_1_2_canonical hDG hAff hCC hW hE hN hL1 hE1 hE3 hB hCamp hDecFrozen hDec hCM hAx hLen hN2 hμW hCanon
      hNonat hExists hfr hmass hCMAbs hCMRew hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hMassM hSupM hFin
      hWIC hM1 hM2 hId hTor)

end Closure

end HarmonicBalls
