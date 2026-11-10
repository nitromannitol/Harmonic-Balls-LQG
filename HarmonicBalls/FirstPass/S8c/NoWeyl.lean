import HarmonicBalls.FirstPass.S8c
import HarmonicBalls.FirstPass.S8c.WeylOffOriginDerived

/-! # FIRST-PASS result 8.2 without the Weyl hypothesis (fp-8-2-noWeyl-and-imports, worker z6)

`firstPass_8_2` (`FirstPass/S8c.lean:30`) takes the frozen Prop `LocalLQGInsertionWeylOffOrigin` as the binder `hWeyl`.
That Prop is derived with no hypotheses by `localLQGInsertionWeylOffOrigin_derived`
(`FirstPass/S8c/WeylOffOriginDerived.lean`). `firstPass_8_2_noWeyl` is `firstPass_8_2` with `hWeyl` removed: its binders
are those of `firstPass_8_2`, in the same order, minus `hWeyl`, and its conclusion is the same
(`TypicalPointManyGoodScalesStmt`). The original theorem is unchanged.

This is the S8c version only. `FirstPass/S8d.lean:32` declares a second theorem with the same full name
`HarmonicBalls.firstPass_8_2`, so the two originals cannot be imported together. The S8d version is
`firstPass_8_2_S8d_noWeyl` (`FirstPass/S8dNoWeyl.lean`). -/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- FIRST-PASS result 8.2 (Lemma 8.2, many good scales at typical points) without the Weyl hypothesis: the S8c proof
`firstPass_8_2` applied to the derived Weyl relation off the origin `localLQGInsertionWeylOffOrigin_derived` in the
slot of `hWeyl`. -/
theorem firstPass_8_2_noWeyl (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hfull : LQGMeasureFullSupportStmt.{u})
    (hTail : LocalPhaseTailStep.{u})
    (hEx : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α hC hcirc) :
    TypicalPointManyGoodScalesStmt.{u} :=
  firstPass_8_2 hL1 hfull localLQGInsertionWeylOffOrigin_derived.{u} hTail hEx hN

end HarmonicBalls
