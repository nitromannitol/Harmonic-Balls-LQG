import HarmonicBalls.Draft.Section1
import HarmonicBalls.Draft.Section11
import HarmonicBalls.FirstPass.S11i.Faithful

/-!
# Canonical-exponent statements of Theorem 1.2 and Proposition 11.11 (FIRST-PASS fp-canonical-stmts-and-novelty, worker z6)

Shared statement definitions for the canonical copy chain of the closures of Theorem 1.2 and Proposition 11.11.
Source: chat 224, Correction 1 (the Lemma 11.13 target is taken at the canonical exponent `ξ = lqgXi γ`,
`FirstPass/S11i/Faithful.lean:94`). The 11.13 target no longer implies the uniform statement over all `ξ`, so the
metric clauses of Theorem 1.2 and Proposition 11.11 are restated with `ξ := lqgXi γ`. The rest of each statement is
copied unchanged from the Draft.

* `HarmonicBallNotMetricBallCanonicalStmt`: body of `HarmonicBallNotMetricBallStmt` (`Draft/Section11.lean:231`) with
  `ξ := lqgXi γ`; the universal quantifier over `ξ` is dropped.
* `HarmonicBallNoveltyCanonicalStmt`: body of `HarmonicBallNoveltyStmt` (`Draft/Section1.lean:124`) with `ξ := lqgXi γ`;
  the universal quantifier over `ξ` in the metric clause is dropped.

The definitions are used by `FirstPass/Canonical/Novelty.lean` and by the Section 11 canonical copies. -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Proposition 11.11 (prop:not-metric-balls, line 3091) at the canonical exponent `ξ = lqgXi γ`, chat 224
Correction 1. Body of `HarmonicBallNotMetricBallStmt` (`Draft/Section11.lean:231`) with `ξ := lqgXi γ`: almost surely,
`Λ̂_t` is not an LQG-metric ball for Lebesgue-a.e. `t > 0`, for the metric `D` of `IsLQGMetricOfField P γ (lqgXi γ) α₀ hC D`. -/
def HarmonicBallNotMetricBallCanonicalStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ (lqgXi γ) α₀ hC D →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) 0) →
  ∀ᵐ ω ∂P, ∀ᵐ t ∂volume, 0 < t → ∀ (w : ℂ) (s : ℝ), Λ ω t ≠ lqgMetricBall (D ω) w s

/-- Theorem 1.2 (theorem:harmonic-balls-properties, `Draft/Section1.lean:124`) at the canonical exponent `ξ = lqgXi γ`,
chat 224 Correction 1. Body of `HarmonicBallNoveltyStmt` with `ξ := lqgXi γ`: the non-Lipschitz and Jordan clauses are
unchanged, and the metric-ball clause is stated for the metric `D` of `IsLQGMetricOfField P γ (lqgXi γ) α₀ hC D`. -/
def HarmonicBallNoveltyCanonicalStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) 0) →
  (∀ᵐ ω ∂P,
    (∀ᵐ t ∂volume, 0 < t → ¬ IsLipschitzDomain (Λ ω t)) ∧
    ∀ t : ℝ, 0 < t → ∀ C ∈ connectedComponentsIn (closure (Λ ω t))ᶜ, IsSimpleLoop (frontier C)) ∧
  ∀ (D : Ω → ℂ → ℂ → ℝ), IsLQGMetricOfField P γ (lqgXi γ) α₀ hC D →
    ∀ᵐ ω ∂P, ∀ᵐ t ∂volume, 0 < t → ∀ (w : ℂ) (s : ℝ), Λ ω t ≠ lqgMetricBall (D ω) w s

end HarmonicBalls
