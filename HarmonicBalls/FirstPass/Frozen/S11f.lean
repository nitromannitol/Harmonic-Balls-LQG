import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Defs.LBM
import HarmonicBalls.Defs.Notation

/-!
# First-pass frozen inputs for Lemmas 11.16 and 11.17 (fp-S11f, owner n2)

FIRST-PASS FROZEN inputs of the Section 11 pinch events. Each is a `def ... : Prop` (never an axiom). Only the
square-diameter tail of Ding-Dubédat-Dunlap-Falconet is frozen here; the paper's own events and their measurability are
NOT frozen (operator ruling 2026-11-09 18:50 UTC).
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology

/-- FIRST-PASS FROZEN. Square-diameter tail of the LQG metric, uniformly on compacts. For a whole-plane GFF `(hC, hcirc)`
on a probability space, the LQG metric `𝔇(hC ω)` of the field `hC ω` (an `IsLQGMetric γ ξ 𝔇` functional, `ξ > 0`), every
compact `K`, and every `0 < s < ξ Q` (`Q = lqgQ γ`), there are a constant `c₁ > 0` and a function `ε` tending to `0` at
`0⁺` such that for all small side lengths `ℓ` and every `w ∈ K`,
`P[ sup_{u,v ∈ S_ℓ(w)} D(u,v; S_ℓ(w)) > ℓ^s c₁ e^{ξ g_1(0)} ] ≤ ℓ^{(ξQ - s)²/(2ξ²) + ε(ℓ)}`,
where `D = 𝔇(hC ω)`, `S_ℓ(w) = closedSquare w ℓ` (lower-left corner `w`; a change of the corner convention moves `K` to a
compact set and does not change the statement) and `g_1(0) = hcirc ω 1 0` is the unit circle average at `0`.
Restated (n2, round 2) from the `IsLQGMetricOfField` form to the metric functional `𝔇(hC ω)`: the same object, since the
realized LQG metric of the field is `𝔇(hC ω)` (`IsLQGMetricOfField` with exponent zero).
Source: Ding, Dubédat, Dunlap, Falconet, Lemma 3.19, equation (3.63), page 45, arXiv:1905.00380v2; the statement as quoted
by Bou-Rabee-Gwynne (arXiv:2208.11795, paper lines 3392-3405, item (ii)), where it is used for the square-diameter tail of
Lemma 11.9 (paper lines 3539-3541).
Used by: firstPass_11_16 (through `PinchSecondMassStep`, once that step is proved; `HarmonicBalls/FirstPass/S11f/DyadicTail.lean`
converts it to the discrete dyadic tail). -/
def DDDFSquareDiameterTailFrozen : Prop :=
  ∀ (γ ξ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → 0 < ξ → IsLQGMetric γ ξ 𝔇 →
    ∀ K : Set ℂ, IsCompact K → ∀ s : ℝ, 0 < s → s < ξ * lqgQ γ →
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ᶠ ℓ in 𝓝[>] (0 : ℝ), ∀ w ∈ K,
        P {ω | ENNReal.ofReal (ℓ ^ s * c₁ * Real.exp (ξ * hcirc ω 1 0)) <
            ⨆ u ∈ closedSquare w ℓ, ⨆ v ∈ closedSquare w ℓ, internalMetric (𝔇 (hC ω)) (closedSquare w ℓ) u v} ≤
          ENNReal.ofReal (ℓ ^ ((ξ * lqgQ γ - s) ^ 2 / (2 * ξ ^ 2) + ε ℓ))

end HarmonicBalls
