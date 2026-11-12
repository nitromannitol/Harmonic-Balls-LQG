import HarmonicBalls.FirstPass.LPBridge.LQGMeasureNonatomicAll
import LatticeProb.LQG.LQGMeasureNonatomicUpper

/-!
# Rows 4 and 41: the γ-LQG measure of a whole-plane GFF has no atoms, at every insertion `α₀`

`LQGMeasureNonatomic P γ α₀ hC hcirc` (`Proposed/LQG.lean:86`, paper Fact 2.1 I): for a whole-plane GFF `h^ℂ`,
`0 < γ < 2` and `α₀ < Q_γ`, almost surely the γ-LQG measure of `h^ℂ - α₀ log|·|` has no atom.

The library proves the same statement in its own definitions with no hypothesis
(`LatticeProb.LQG.LQGMeasureNonatomicUpper.lqgMeasureNonatomicLP_holds`, module
`LatticeProb.LQG.LQGMeasureNonatomicUpper`: the upper tail of ball masses from the positive moments, Borel-Cantelli in the
unit square, integer translates, the Weyl identity off the origin and a stronger insertion at the origin; the lower tail of
ball masses is not used). `LPBridge.lqgMeasureNonatomic_of_lp` (`LPBridge/LQGMeasureNonatomicAll.lean`) transports it.
-/

universe u v

namespace HarmonicBalls

open MeasureTheory

/-- Row 4 holds at every insertion `α₀`: non-atomicity of the γ-LQG measure of a whole-plane GFF, for every probability
space in universe `u` (the hypothesis `hN` of the Section 8 forms). -/
theorem lqgMeasureNonatomic_holds :
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc :=
  fun _ _ P γ α₀ hC hcirc =>
    LPBridge.lqgMeasureNonatomic_of_lp P γ α₀ hC hcirc
      (LatticeProb.LQG.LQGMeasureNonatomicUpper.lqgMeasureNonatomicLP_holds P γ α₀ hC hcirc)

/-- Row 41 holds: `S11n.MeasureDecoder.LQGMeasureNonatomicAll` (exponents before the probability space), in every
universe. -/
theorem lqgMeasureNonatomicAll_holds : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{v} :=
  fun γ α₀ Ω _ P hC hcirc => lqgMeasureNonatomic_holds.{v} Ω P γ α₀ hC hcirc

end HarmonicBalls
