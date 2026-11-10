import HarmonicBalls.Proposed.LQGDimension
import HarmonicBalls.FirstPass.Closure.Sec11
import HarmonicBalls.FirstPass.Closure.Sec11Canonical
import HarmonicBalls.FirstPass.Closure.Main12Canonical

/-! # Paper-exponent records of the canonical closures (FIRST-PASS fp-canonical-paper-exponent, worker z4)

The canonical closures `closure_11_13_canonical`, `closure_11_11_canonical` and `closure_1_2_faithful_canonical` are
stated at the exponent `ξ = lqgXi γ`, where `lqgXi γ = γ / lqgGraphDimension γ` (`HarmonicBalls/FirstPass/S11i/Faithful.lean:94`).
That identity is the paper's exponent `ξ = γ / d_γ` (eq:xi, `paper/lqg_harmonic_ball-corrected.tex:443`) only under the
PROPOSED input `WholePlaneLQGGraphDimension` (`HarmonicBalls/Proposed/LQGDimension.lean:20`, pending operator
source-check; characterisation `lqgGraphDimension_spec`, `Proposed/LQGDimension.lean:24`, from Ding-Gwynne
arXiv:1807.01072, Theorem 1.4).

Operator decision 11:42 UTC (F2): the input is kept as an explicit first hypothesis `_hDim` of each wrapper below, so that
no statement claims that `lqgXi` is the paper exponent without it. The wrappers record the dimension input explicitly;
it is not used in the proof; no new frozen input. Each wrapper has the binders of the wrapped theorem in their order,
and the conclusion of the wrapped theorem. -/

namespace HarmonicBalls.Closure

open MeasureTheory Metric Set Filter Topology

universe u

/-- Paper-exponent record of `closure_11_13_canonical` (`FirstPass/Closure/Sec11.lean:400`): Lemma 11.13 at the canonical
exponent `ξ = lqgXi γ` (`FirstPass/S11i/Faithful.lean:94`). The identity `lqgXi γ = γ / d_γ` with the paper's eq:xi
(`paper/lqg_harmonic_ball-corrected.tex:443`) holds under `WholePlaneLQGGraphDimension` (`Proposed/LQGDimension.lean:20`,
PROPOSED, pending operator source-check; spec `lqgGraphDimension_spec`, :24). Operator 11:42 UTC (F2). The dimension input
is recorded in `_hDim` explicitly; it is not used in the proof; no new frozen input. Conclusion: `CorrectedLemma11_13CanonicalStmt`. -/
theorem closure_11_13_paperExponent
    (_hDim : WholePlaneLQGGraphDimension)
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hLen : LQGMetricLengthUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hμW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hmass : LQGMassFunctionalMeasurableFrozen.{u})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{u})
    (hCMRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u}) (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u}) (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u}) (hMassM : LQGMeasureSquareMeasurableFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u}) (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hW : WeylInternalClosedFrozen)
    (hM1 : WeylShiftedSupMeasurableFrozen.{u}) (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u}) :
    CorrectedLemma11_13CanonicalStmt.{u} :=
  closure_11_13_canonical hAx hLen hN2 hμW hLoc hCanon hNonat hExists hDG hCC hE hfr hmass hCMAbs hCMRew
    hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hMassM hSupM hFin hW hM1 hM2 hId

/-- Paper-exponent record of `closure_11_11_canonical` (`FirstPass/Closure/Sec11Canonical.lean:37`): Proposition 11.11 at
the canonical exponent `ξ = lqgXi γ` (`FirstPass/S11i/Faithful.lean:94`). The identity `lqgXi γ = γ / d_γ` with the paper's
eq:xi (`paper/lqg_harmonic_ball-corrected.tex:443`) holds under `WholePlaneLQGGraphDimension` (`Proposed/LQGDimension.lean:20`,
PROPOSED, pending operator source-check; spec `lqgGraphDimension_spec`, :24). Operator 11:42 UTC (F2). The dimension input
is recorded in `_hDim` explicitly; it is not used in the proof; no new frozen input. Conclusion: `HarmonicBallNotMetricBallCanonicalStmt`. -/
theorem closure_11_11_paperExponent
    (_hDim : WholePlaneLQGGraphDimension)
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u}) (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hLen : LQGMetricLengthUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hμW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
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
    (hShift : LQGMetricContinuousShiftFactI.{u}) (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u}) (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u}) (hMassM : LQGMeasureSquareMeasurableFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u}) (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hWIC : WeylInternalClosedFrozen)
    (hM1 : WeylShiftedSupMeasurableFrozen.{u}) (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u}) :
    HarmonicBallNotMetricBallCanonicalStmt.{u} :=
  closure_11_11_canonical hDG hCC hE hW hN hL1 hE1 hE3 hB hAx hLen hN2 hμW hLoc hCanon hNonat hExists
    hfr hmass hCMAbs hCMRew hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hMassM hSupM hFin
    hWIC hM1 hM2 hId

/-- Paper-exponent record of `closure_1_2_faithful_canonical` (`FirstPass/Closure/Main12Canonical.lean:182`): Theorem 1.2
at the canonical exponent `ξ = lqgXi γ` (`FirstPass/S11i/Faithful.lean:94`). The identity `lqgXi γ = γ / d_γ` with the paper's
eq:xi (`paper/lqg_harmonic_ball-corrected.tex:443`) holds under `WholePlaneLQGGraphDimension` (`Proposed/LQGDimension.lean:20`,
PROPOSED, pending operator source-check; spec `lqgGraphDimension_spec`, :24). Operator 11:42 UTC (F2). The dimension input
is recorded in `_hDim` explicitly; it is not used in the proof; no new frozen input. Conclusion: `HarmonicBallNoveltyFaithfulStmt`. -/
theorem closure_1_2_paperExponent
    (_hDim : WholePlaneLQGGraphDimension)
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
  closure_1_2_faithful_canonical hDG hAff hCC hW hE hN hL1 hE1 hE3 hB hCamp hDecFrozen hDec hCM hAx hLen
    hN2 hμW hCanon hNonat hExists hfr hmass hCMAbs hCMRew hComp hMf hDiam hMk hholder hShift hFD hDC hCMT
    hPos10 hMassM hSupM hFin hWIC hM1 hM2 hId hTor

#print axioms closure_11_13_paperExponent
#print axioms closure_11_11_paperExponent
#print axioms closure_1_2_paperExponent

end HarmonicBalls.Closure
