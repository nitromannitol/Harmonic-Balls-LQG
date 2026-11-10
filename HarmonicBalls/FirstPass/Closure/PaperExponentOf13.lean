import HarmonicBalls.Proposed.LQGDimension
import HarmonicBalls.FirstPass.Closure.Sec11CanonicalOf13
import HarmonicBalls.FirstPass.Closure.Main12CanonicalOf13

/-! # Paper-exponent records of the counted canonical closures, fed by the numbered Lemma 11.13
(FIRST-PASS fp-counted-paper-exponent-of-11-13, worker z4)

The counted canonical closures `closure_11_11_canonical_of_11_13` (`FirstPass/Closure/Sec11CanonicalOf13.lean:29`) and
`closure_1_2_faithful_canonical_of_11_13` (`FirstPass/Closure/Main12CanonicalOf13.lean:70`) take the numbered canonical
Lemma 11.13, `h13 : CorrectedLemma11_13CanonicalStmt` (`FirstPass/S11i/Faithful.lean:102`), in place of the internal part (d)
`Step8IdentityGivenPinchEventCanonicalStmt`. They are stated at the exponent `ξ = lqgXi γ`
(`FirstPass/S11i/Faithful.lean:94`). That identity is the paper's exponent `ξ = γ / d_γ` (eq:xi,
`paper/lqg_harmonic_ball-corrected.tex:443`) only under the PROPOSED input `WholePlaneLQGGraphDimension`
(`HarmonicBalls/Proposed/LQGDimension.lean:19`, pending operator source-check).

As in `FirstPass/PaperExponent.lean` (operator decision 11:42 UTC, F2), the dimension input is an explicit first hypothesis
`_hDim` of each wrapper. It is not used in the proof, and no new frozen input is introduced. Each wrapper has the binders of
the wrapped theorem in their order, and the conclusion of the wrapped theorem. -/

namespace HarmonicBalls.Closure

open MeasureTheory Metric Set Filter Topology

universe u

/-- Paper-exponent record of `closure_11_11_canonical_of_11_13` (`FirstPass/Closure/Sec11CanonicalOf13.lean:29`):
Proposition 11.11 at the canonical exponent `ξ = lqgXi γ`, with the numbered Lemma 11.13 `h13` as input. The dimension
input `WholePlaneLQGGraphDimension` (`Proposed/LQGDimension.lean:19`, PROPOSED) is recorded in `_hDim`; it is not used.
Conclusion: `HarmonicBallNotMetricBallCanonicalStmt`. -/
theorem closure_11_11_paperExponent_of_11_13
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
    (h13 : CorrectedLemma11_13CanonicalStmt.{u}) :
    HarmonicBallNotMetricBallCanonicalStmt.{u} :=
  closure_11_11_canonical_of_11_13 hDG hCC hE hW hN hL1 hE1 hE3 hB hAx h13

/-- Paper-exponent record of `closure_1_2_faithful_canonical_of_11_13` (`FirstPass/Closure/Main12CanonicalOf13.lean:70`):
Theorem 1.2 (faithful form) at the canonical exponent `ξ = lqgXi γ`, with the numbered Lemma 11.13 `h13` as input. The
dimension input `WholePlaneLQGGraphDimension` (`Proposed/LQGDimension.lean:19`, PROPOSED) is recorded in `_hDim`; it is not used.
Conclusion: `HarmonicBallNoveltyFaithfulStmt`. -/
theorem closure_1_2_paperExponent_of_11_13
    (_hDim : WholePlaneLQGGraphDimension)
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
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (h13 : CorrectedLemma11_13CanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallNoveltyFaithfulStmt.{u} :=
  closure_1_2_faithful_canonical_of_11_13 hDG hAff hCC hW hE hN hL1 hE1 hE3 hB hCamp hDecFrozen hDec hCM hAx h13 hTor

#print axioms closure_11_11_paperExponent_of_11_13
#print axioms closure_1_2_paperExponent_of_11_13

end HarmonicBalls.Closure
