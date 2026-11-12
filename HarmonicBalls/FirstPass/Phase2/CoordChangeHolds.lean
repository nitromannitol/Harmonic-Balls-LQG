import HarmonicBalls.FirstPass.Phase2.CoordChangeZeroHolds
import HarmonicBalls.FirstPass.S11i.Step8PhysReduction
import LatticeProb.LQG.GMCContinuumMaximal

/-!
# Row 2 at every `α₀`: the coordinate change rule of the γ-LQG measure of a whole-plane GFF

`LQGMeasureCoordChange P γ α₀ hC hcirc` (`Proposed/LQG.lean:131`): for a whole-plane GFF `h^ℂ`, `0 < γ < 2` and
`α₀ < Q_γ`, almost surely, for every `a ≠ 0` and `b`, the push-forward of the γ-LQG measure of `h^ℂ - α₀ log|·|`
under `x ↦ (x - b)/a` is the γ-LQG limit of the circle averages
`ε, z ↦ h_{|a| ε}(a z + b) - α₀ log |a z + b| + Q_γ log |a|` (Duplantier-Sheffield 2011, Proposition 2.1; simultaneously
over all complex affine maps as in Sheffield-Wang, arXiv:1605.06171, Theorems 1.1 and 1.4).

The library proves the same statement in its own definitions for every `α₀`
(`LatticeProb.LQG.coordChangeLP_of_isWholePlaneGFF`, module `LatticeProb.LQG.GMCContinuumMaximal`: the circle-average
approximations along every ratio sequence `r 2^{-k}` converge to the same γ-LQG measure, the logarithmic insertion
being controlled by the maximal continuum masses at the origin). `lqgMeasureCoordChange_of_lpForm`
(`Phase2/CoordChangeZeroHolds.lean`) transports it to the HB definitions. This supersedes
`lqgMeasureCoordChange_zero_holds` (the case `α₀ = 0`).
-/

universe u v

namespace HarmonicBalls

open MeasureTheory

/-- Row 2 holds at every insertion `α₀`: the coordinate change rule of the γ-LQG measure of a whole-plane GFF, for
every probability space in universe `u`, every `γ`, every `α₀` and every circle-average process (the hypothesis `hCC`
of the Section 2 and Section 11 forms that bind it at a general `α₀`). -/
theorem lqgMeasureCoordChange_holds :
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc :=
  fun _ _ P γ α₀ hC hcirc =>
    lqgMeasureCoordChange_of_lpForm P γ α₀ hC hcirc
      (LatticeProb.LQG.coordChangeLP_of_isWholePlaneGFF P γ α₀ hC hcirc)

/-- The coordinate change rule in the binder order of `CoordChangeAlpha0Stmt` (`S11i/Step8PhysReduction.lean:81`,
exponents before the probability space) holds, in every universe. -/
theorem coordChangeAlpha0Stmt_holds :
    HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{v} :=
  fun γ α₀ Ω _ P hC hcirc => lqgMeasureCoordChange_holds.{v} Ω P γ α₀ hC hcirc

end HarmonicBalls
