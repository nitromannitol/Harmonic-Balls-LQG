import HarmonicBalls.FirstPass.Closure.Sec11

/-!
# Lemma 11.13 (canonical): assembly map with every available provider (fp-S11-13-assembly-map, owner n3)

`HarmonicBalls.FirstPassS11iAssembly11_13.firstPass_11_13_canonical` concludes `CorrectedLemma11_13CanonicalStmt`
(`HarmonicBalls/FirstPass/S11i/Faithful.lean:102`) exactly. The declaration sits in the namespace
`FirstPassS11iAssembly11_13` because `HarmonicBalls.firstPass_11_13_canonical` already exists
(`HarmonicBalls/FirstPass/S11i/Corrected11_13.lean:127`, binders `hAx`, `hMeas`, `hPE`, `hId`).

Route (the one closest to done): `HarmonicBalls.Closure.closure_11_13_canonical`
(`HarmonicBalls/FirstPass/Closure/Sec11.lean:400`), whose proof plugs in the providers below.
* Part (c), `Step8PinchEventCanonicalStmt`: `closure_11_12` (`Closure/Sec11.lean:357`, fed by binders 1 to 31 below), then
  `pinchEventGamma_exists` (`HarmonicBalls/FirstPass/S11i/Step8Event.lean:89`).
* Glue: `firstPass_11_13_canonical` (`S11i/Corrected11_13.lean:127`), with `hAx` (binder 1) and `hMeas` := `hE` (binder 11).
* Part (d), `Step8IdentityGivenPinchEventCanonicalStmt` (binder 32): the only OPEN binder. No repository theorem concludes it.
  The Step 8 pieces that are landing are not yet a provider: `ae_quantum_bad_mass_eq_zero_of_rootedLocalIdent`
  (`HarmonicBalls/FirstPass/S11ai/RootedAssembly.lean:39`), `ae_rootedLocalIdent_assembled_kernel`
  (`HarmonicBalls/FirstPass/S11r/RootedBufferKernel.lean:27`), `href_discNormalized_doubledDisc_finiteKernel`
  (`HarmonicBalls/FirstPass/S11i/Step8HrefBall.lean:135`); their conclusions are not `Step8IdentityGivenPinchEventCanonicalStmt`.

Binder classes. Abbreviation `FP/` = `HarmonicBalls/FirstPass/`.
* FROZEN: a first-pass frozen axiom (`FP/Frozen/*.lean`, `FP/S11r/Frozen.lean`), or a cited Draft statement
  (`GreenPotentialHolderStmt`, `Draft/Section2.lean:190`, Proposition 2.5, Green clause, listed in `docs/campaign/FROZEN.md`).
  No repository theorem concludes any of these Props.
* PROPOSED: a literature input staged in `HarmonicBalls/Proposed/LQG.lean`, pending operator source-check.
* OPEN: no provider, not frozen.

The 32 binders, in order:
1. `hAx` `LQGMetricFieldAxiomsUnivFrozen`: FROZEN, `FP/Frozen/S11j.lean:155`.
2. `hLen` `LQGMetricLengthUnivFrozen`: FROZEN, `FP/Frozen/S11j.lean:133`.
3. `hN2` `LocalMetricReplacementStmt` (all `γ ξ`, disks in `ball 0 1` form): OPEN. Not in a `Frozen/` file; the
   operator's 04:48 UTC note keeps it as an input; n2's B2 target, `FP/S11r/LocalMetricReplacement.lean:58`, unproved.
4. `hμW` `LQGMeasureWeylScaling`: PROPOSED, `Proposed/LQG.lean:95`.
5. `hLoc` `LocalLQGDecoderCommonFrozen`: FROZEN, `FP/Frozen/S11c.lean:388`.
6. `hCanon` `LQGCanonicalDecodersExistStmt`: FROZEN, `FP/Frozen/S11n.lean:33`.
7. `hNonat` `LQGMeasureNonatomicAll`: PROPOSED, `FP/S11n/MeasureDecoder.lean:39` (of `Proposed/LQG.lean:77`).
8. `hExists` `WholePlaneGFFExistsFrozen`: FROZEN, `FP/S11r/Frozen.lean:39`.
9. `hDG` `WholePlaneLQGBallMassBounds`: PROPOSED, `Proposed/LQG.lean:154`.
10. `hCC` `LQGMeasureCoordChange P γ 0`: PROPOSED, `Proposed/LQG.lean:116`.
11. `hE` `LQGMeasureExistence P γ α`: PROPOSED, `Proposed/LQG.lean:68`.
12. `hfr` `LQGInternalMetricWeylAeMeasurableFrozen`: FROZEN, `FP/Frozen/S11d.lean:130`.
13. `hmass` `LQGMassFunctionalMeasurableFrozen`: FROZEN, `FP/Frozen/S11d.lean:155`.
14. `hCMAbs` `CameronMartinGFFMutualAbsCont`: FROZEN, `FP/Frozen/S11d.lean:74`.
15. `hCMRew` `S11aj.CameronMartinGFFReweighting`: FROZEN, `FP/Frozen/S11aj.lean:33`.
16. `hComp` `WeylScalingCompositionFrozen`: FROZEN, `FP/Frozen/S11d.lean:91`.
17. `hMf` `LQGMassInnerMeasurableFrozen`: FROZEN, `FP/Frozen/S11k.lean:66`.
18. `hDiam` `LQGInternalDiamInnerMeasurableFrozen`: FROZEN, `FP/Frozen/S11k.lean:89`.
19. `hMk` `DomainMarkovConditionalPositiveFrozen`: FROZEN, `FP/Frozen/S11k.lean:45`.
20. `hholder` `GreenPotentialHolderStmt`: FROZEN (cited), `Draft/Section2.lean:190`.
21. `hShift` `LQGMetricContinuousShiftFactI`: FROZEN, `FP/Frozen/S11d.lean:34`.
22. `hFD` `PlaneDomainMinusConvexCompactPreconnectedFrozen`: FROZEN, `FP/Frozen/S11d.lean:26`.
23. `hDC` `DyadicCellDiamSmallFrozen`: FROZEN, `FP/Frozen/S11c.lean:67`.
24. `hCMT` `CameronMartinEventTransferFrozen`: FROZEN, `FP/Frozen/S11c.lean:149`.
25. `hPos10` `LQGMeasureSquarePositiveFrozen`: FROZEN, `FP/Frozen/S11c.lean:130`.
26. `hMassM` `LQGMeasureSquareMeasurableFrozen`: FROZEN, `FP/Frozen/S11c.lean:117`.
27. `hSupM` `LQGMetricSupMeasurableFrozen`: FROZEN, `FP/Frozen/S11c.lean:105`.
28. `hFin` `ConnectedSquareUnionDiamFiniteFrozen`: FROZEN, `FP/Frozen/S11c.lean:91`.
29. `hW` `WeylInternalClosedFrozen`: FROZEN, `FP/Frozen/S11c.lean:180`.
30. `hM1` `WeylShiftedSupMeasurableFrozen`: FROZEN, `FP/Frozen/S11c.lean:217`.
31. `hM2` `WeylShiftedMassMeasurableFrozen`: FROZEN, `FP/Frozen/S11c.lean:233`.
32. `hId` `Step8IdentityGivenPinchEventCanonicalStmt`: OPEN, part (d) of Lemma 11.13 (Step 8 of the corrected proof of
   `lemma:mu_h-pinch-bad`, corrected lines 3848-3930), `FP/S11i/Corrected11_13.lean:109`. No provider.

Binders 1 to 31 are exactly the binders of `closure_11_13_canonical`; binder 32 is its only open input. The proof is the
call of `closure_11_13_canonical`; nothing is weakened.
-/

universe u

namespace HarmonicBalls.FirstPassS11iAssembly11_13

open MeasureTheory

/-- **Lemma 11.13 (canonical), assembly.** `CorrectedLemma11_13CanonicalStmt` from the frozen and proposed inputs
(binders 1 to 31, classes in the module docstring) and the single OPEN named input `hId`, part (d) of the Step 8
identification at the canonical Weyl exponent `ξ = lqgXi γ`. Part (c), the Lemma 11.12 event, is provided by `closure_11_12`
and `pinchEventGamma_exists`; the glue is `firstPass_11_13_canonical` (`FP/S11i/Corrected11_13.lean:127`). -/
theorem firstPass_11_13_canonical
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
  HarmonicBalls.Closure.closure_11_13_canonical hAx hLen hN2 hμW hLoc hCanon hNonat hExists hDG hCC hE hfr hmass
    hCMAbs hCMRew hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hMassM hSupM hFin hW hM1 hM2 hId

end HarmonicBalls.FirstPassS11iAssembly11_13

#print axioms HarmonicBalls.FirstPassS11iAssembly11_13.firstPass_11_13_canonical
