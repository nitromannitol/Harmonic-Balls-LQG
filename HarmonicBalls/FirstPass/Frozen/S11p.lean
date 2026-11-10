import HarmonicBalls.Defs.GFF

/-!
# First-pass frozen input for Lemma 11.16: circle averages as limits of pairings (fp-S11p, owner n4)

One EXTERNAL Prop used by `FirstPass/S11p/ModConstComposition.lean` to recover the additive constant of the
whole-plane GFF from pairings with test functions supported outside `closure W`. The normalisation
`h^ℂ_1(0) = 0` is NOT frozen: it is the theorem `IsWholePlaneGFF.ae_circleAverage_one_zero` (`Defs/GFF.lean`).
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology

universe u

/-- FIRST-PASS FROZEN. Circle averages of the whole-plane GFF are almost sure limits of pairings with unit-mass test
functions concentrating on the circle (EXTERNAL; Duplantier-Sheffield, arXiv:0808.1560v2, Section 3.1 and Proposition
3.1; Bou-Rabee-Gwynne, arXiv:2208.11795v3, eq. (2.6)). Truth check: PENDING (proof idea: take radial unit-mass bumps
`ψ_j` around `z` with support shrinking to the circle `sphere z r`; then `(h^ℂ, ψ_j)` is the average of `h^ℂ_s(z)` over
`s` against a unit-mass profile, which tends to `h^ℂ_r(z)` by the a.s. joint continuity of `(s, z) ↦ h^ℂ_s(z)`,
`IsWholePlaneGFF.ae_continuousOn_circle`). Locator: operator source-check pending.

Statement: for every whole-plane GFF `(P, hC, hcirc)`, every open `O` containing the circle `sphere z r` (`0 < r`), there
is a sequence `ψ_j` of test functions with `tsupport ψ_j ⊆ O` and `∫ ψ_j = 1` such that almost surely
`hC ω (ψ_j) → hcirc ω r z`. -/
def WholePlaneCircleAverageLimitFrozen : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    ∀ (O : Set ℂ) (r : ℝ) (z : ℂ), IsOpen O → 0 < r → sphere z r ⊆ O →
      ∃ ψ : ℕ → ℂ → ℝ, (∀ j, IsTestFunction O (ψ j) ∧ ∫ x, ψ j x = 1) ∧
        ∀ᵐ ω ∂P, Tendsto (fun j => hC ω (ψ j)) atTop (𝓝 (hcirc ω r z))

end HarmonicBalls
