import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQGMetric

/-!
# Frozen input: Cameron-Martin reweighting of the whole-plane GFF

FROZEN input for the shifted clause of `FirstPass/S11aj.lean`. Moved verbatim from `FirstPass/S11aj.lean`
(statement unchanged, same namespace `HarmonicBalls.S11aj`, same universe). It is a `def ... : Prop`, never an axiom,
used as a named hypothesis by `FirstPass/S11aj.lean` and `FirstPass/S11an.lean`.
-/

universe u

namespace HarmonicBalls.S11aj

open MeasureTheory Set Metric
open scoped ENNReal

/-- DERIVED INTERFACE. "The Radon–Nikodym/reweighting
identity is standard, but the exact normalization and arbitrary-carrier Lean interface must be derived."
FROZEN. Cameron-Martin reweighting of the whole-plane GFF (Miller-Sheffield, Imaginary Geometry IV,
arXiv:1302.4738v2, Proposition 2.9, printed p. 49; Gaussian tilting). Truth check TRUE exactly as typed, including the
joint law with the circle averages `hcirc`.
The Cameron-Martin theorem for the whole-plane GFF: for every whole-plane GFF `(P, hC, hcirc)` and every smooth compactly
supported `f` with zero unit-circle average, there is a measure `P'` equivalent to `P` under which the shifted pairings
`addFunPairing (hC ω) f` and the shifted circle averages `hcirc ω r z + Av_{∂B_r(z)} f` form a whole-plane GFF.

Why this is a named hypothesis and not a consequence of `CameronMartinGFFMutualAbsCont` (`Frozen/S11d.lean:74`): that
frozen input gives only equality of null sets for events of `distributionMeasurableSpace`, i.e. for pairings. A
Radon-Nikodym density `dP'/dP` that makes the circle averages GFF-distributed needs equivalence of the joint laws of
`(hC, hcirc)` and `(hC + f, hcirc + Av f)`, and the circle averages are not `distributionMeasurableSpace`-measurable
functions of `hC` (no input supplies that). -/
def CameronMartinGFFReweighting : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → ∀ f : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
    HasCompactSupport f → Real.circleAverage f 0 1 = 0 →
    ∃ P' : Measure Ω, P' ≪ P ∧ P ≪ P' ∧
      IsWholePlaneGFF P' (fun ω => addFunPairing (hC ω) f)
        (fun ω r z => hcirc ω r z + Real.circleAverage f z r)

end HarmonicBalls.S11aj
