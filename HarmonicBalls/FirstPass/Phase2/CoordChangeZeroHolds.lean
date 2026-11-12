import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import LatticeProb.LQG.GMCRatioLimitMeasure

/-!
# Row 2 at `α₀ = 0`: the coordinate change rule of the γ-LQG measure of a whole-plane GFF

`LQGMeasureCoordChange P γ 0 hC hcirc` (`Proposed/LQG.lean:131` at `α₀ = 0`): for a whole-plane GFF `h^ℂ` and
`0 < γ < 2`, almost surely, for every `a ≠ 0` and `b`, the push-forward of the γ-LQG measure `μ_h` under
`x ↦ (x - b)/a` is the γ-LQG limit of the circle averages `ε, z ↦ h_{|a| ε}(a z + b) + Q_γ log |a|`
(Duplantier-Sheffield 2011, Proposition 2.1; simultaneously over all affine maps as in Sheffield-Wang,
arXiv:1605.06171, Theorems 1.1 and 1.4).

The library proves the same statement in its own definitions (`LatticeProb.LQG.lqgMeasureCoordChangeLP_zero`, module
`LatticeProb.LQG.GMCRatioLimitMeasure`: the circle-average approximations along every ratio sequence `r 2^{-k}`
converge to the same γ-LQG measure). The definitions match through `LPBridge.isWholePlaneGFF_iff`,
`LPBridge.isLQGMeasureOfField_iff` and `LPBridge.isLQGLimit_iff`; `lqgMeasureCoordChangeLP_of_HB`
(`Phase2/DerivedInputs30.lean`) is the converse transport.
-/

universe u

namespace HarmonicBalls

open MeasureTheory

/-- The library form `LatticeProb.LQG.LQGMeasureCoordChangeLP` of the coordinate change rule gives the HB form
`LQGMeasureCoordChange`, for the same field, exponents and circle-average process. -/
theorem lqgMeasureCoordChange_of_lpForm {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (h : LatticeProb.LQG.LQGMeasureCoordChangeLP P γ α₀ hC hcirc) :
    LQGMeasureCoordChange P γ α₀ hC hcirc := by
  intro hG hγ hγ2 hα μ hμ
  filter_upwards [h ((LPBridge.isWholePlaneGFF_iff P hC hcirc).1 hG) hγ hγ2 hα μ
    ((LPBridge.isLQGMeasureOfField_iff P γ α₀ hcirc μ).1 hμ)] with ω hω a ha b
  exact (LPBridge.isLQGLimit_iff _ _ _).2 (hω a ha b)

/-- Row 2 at `α₀ = 0` holds: the coordinate change rule of the γ-LQG measure of a whole-plane GFF, for every
probability space in universe `u`, every `γ` and every circle-average process (the hypothesis `hCC` of the
Section 11 forms). -/
theorem lqgMeasureCoordChange_zero_holds :
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc :=
  fun _ _ P γ hC hcirc =>
    lqgMeasureCoordChange_of_lpForm P γ 0 hC hcirc (LatticeProb.LQG.lqgMeasureCoordChangeLP_zero P γ hC hcirc)

end HarmonicBalls
