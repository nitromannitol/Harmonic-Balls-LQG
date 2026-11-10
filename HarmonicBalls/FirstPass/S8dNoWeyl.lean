import HarmonicBalls.FirstPass.S8d
import HarmonicBalls.FirstPass.S8c.WeylOffOriginDerived

/-! # FIRST-PASS result 8.2 without the Weyl hypothesis, S8d version (fp-8-2-noWeyl-and-imports, worker z6)

`FirstPass/S8d.lean:32` declares `firstPass_8_2` (the S8d proof, the one used by the closure chain
`Closure/Sec78910.lean` and `Closure/SecA45.lean`). It takes the frozen Prop `LocalLQGInsertionWeylOffOrigin` as the
binder `hWeyl`. That Prop is derived with no hypotheses by `localLQGInsertionWeylOffOrigin_derived`
(`FirstPass/S8c/WeylOffOriginDerived.lean`).

`firstPass_8_2_S8d_noWeyl` is the S8d `firstPass_8_2` with `hWeyl` removed: its binders are those of the S8d theorem,
in the same order, minus `hWeyl`, and its conclusion is the same (`TypicalPointManyGoodScalesStmt`). The original
theorem is unchanged. The S8c theorem of the same full name `HarmonicBalls.firstPass_8_2` (`FirstPass/S8c.lean:30`)
cannot be imported together with `FirstPass/S8d.lean`; its version is `firstPass_8_2_noWeyl`
(`FirstPass/S8c/NoWeyl.lean`), which is not imported by the closure chain. -/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- FIRST-PASS result 8.2 (Lemma 8.2, many good scales at typical points), S8d proof, without the Weyl hypothesis:
the S8d `firstPass_8_2` applied to the derived Weyl relation off the origin `localLQGInsertionWeylOffOrigin_derived` in
the slot of `hWeyl`. -/
theorem firstPass_8_2_S8d_noWeyl (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hfull : LQGMeasureFullSupportStmt.{u})
    (hL67 : VeryGoodAnnulusProbabilityStmt.{u})
    (hEx : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u}) (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0}) :
    TypicalPointManyGoodScalesStmt.{u} :=
  firstPass_8_2 hL1 hfull localLQGInsertionWeylOffOrigin_derived.{u} hL67 hEx hN hAff hCC hE1 hE3 hB

end HarmonicBalls
