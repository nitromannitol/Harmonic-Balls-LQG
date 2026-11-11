import HarmonicBalls.FirstPass.Closure.Sec11Canonical

/-!
# Proposition 11.11 (canonical) from the numbered Lemma 11.13

`closure_11_11_canonical` (`FirstPass/Closure/Sec11Canonical.lean:37`) takes the internal part (d) of Lemma 11.13,
`Step8IdentityGivenPinchEventCanonicalStmt`, and rebuilds the numbered Lemma 11.13 from it through
`closure_11_13_canonical`. This file takes the numbered Lemma 11.13 itself, `CorrectedLemma11_13CanonicalStmt`
(`FirstPass/S11i/Faithful.lean:102`), as the single input `h13`, and passes it to
`manyPinchScalesCanonicalModel_of_canonical` (`FirstPass/Closure/Bridge12Canonical.lean:54`).

Only the block of inputs of `closure_11_13_canonical` (and `hId`) is replaced by `h13`. The remaining binders are those of
`closure_11_11_canonical`, and each of them is used by the proof. `closure_11_11_canonical` itself is unchanged.
-/

universe u

namespace HarmonicBalls.Closure

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- **Proposition 11.11, canonical form, from the numbered Lemma 11.13.** Conclusion
`HarmonicBallNotMetricBallCanonicalStmt` (`FirstPass/Canonical/Stmts.lean`), with the canonical Weyl exponent
`ξ = lqgXi γ` and the model fixed before the density. The input is the numbered `CorrectedLemma11_13CanonicalStmt`
(Lemma 11.13 of the corrected paper, `lemma:mu_h-pinch-bad`), passed through `manyPinchScalesCanonicalModel_of_canonical`.
The hypotheses `hDG`, `hCC`, `hE`, `hW`, `hN`, `hL1`, `hE1`, `hE3`, `hB` and `hAx` are those of
`closure_11_11_canonical`, and each is used by the assembly. -/
theorem closure_11_11_canonical_of_11_13
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
  firstPass_11_11_canonical
    (closure_11_6 hDG hCC hE hW hN hL1 localLQGInsertionWeylOffOrigin_derived hE1 hE3 hB)
    (manyPinchScalesCanonicalModel_of_canonical h13)
    (volumeGrowthI2_of_staged hDG hCC hW hE hN)
    (fun γ α₀ ξ _ _ _ Ω _ P hC hcirc _ => hAx Ω P γ ξ α₀ hC hcirc)

/-- **Counted form of Proposition 11.11** (`prop:not-metric-balls`, arbitrary carrier
`Ω : Type u` and all real radii `s`). Statement `HarmonicBallNotMetricBallCanonicalStmt` at the canonical exponent
`ξ = lqgXi γ`, with the numbered Lemma 11.13 `CorrectedLemma11_13CanonicalStmt` as the single input `h13`. Same binders
and conclusion as `closure_11_11_canonical_of_11_13` (`FirstPass/Closure/Sec11CanonicalOf13.lean:29`), proved by applying it.
Ledger: `hE1` is an occurrence of `LQGMeasureOfProfileMeasurableFrozen`; `hAx` is a universal-ξ external interface (harmless). -/
theorem firstPass_11_11_faithful
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
    (hL1 : LocalRootedFieldMeasureDomination.{u}) (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0}) (hB : BirkhoffPointwiseErgodic.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (h13 : CorrectedLemma11_13CanonicalStmt.{u}) :
    HarmonicBallNotMetricBallCanonicalStmt.{u} :=
  closure_11_11_canonical_of_11_13 hDG hCC hE hW hN hL1 hE1 hE3 hB hAx h13

end HarmonicBalls.Closure
