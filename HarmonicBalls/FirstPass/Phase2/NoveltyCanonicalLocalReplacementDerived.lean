import HarmonicBalls.FirstPass.Phase2.DerivedInputs47
import HarmonicBalls.FirstPass.Phase2.PinchScalesLocalReplacementDerived

/-!
# Theorem 1.2 (canonical exponent) from the local metric replacement alone

Theorem 1.2 at the canonical exponent `ξ = γ / d_γ` (`HarmonicBallNoveltyCanonicalStmt`) holds from Proposition 11.11 at
the canonical exponent (`harmonicBallNoveltyStmt_of_existence_and_results_canonical_derivedInputs47`), and Proposition
11.11 at the canonical exponent holds from the local metric replacement `LocalMetricReplacementStmt` alone
(`harmonicBallNotMetricBallCanonical_of_localMetricReplacement_derived`). Composing the two, the only hypothesis of
Theorem 1.2 at the canonical exponent is the local metric replacement, a statement about the LQG metric
(Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380), and no longer a numbered result of the paper.
-/

namespace HarmonicBalls

universe u

/-- **Theorem 1.2 (canonical exponent, every universe), derived** from the local metric replacement `hN2` alone,
through Proposition 11.11 at the canonical exponent. -/
theorem harmonicBallNoveltyCanonical_of_localMetricReplacement_derived
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂) :
    HarmonicBallNoveltyCanonicalStmt.{u} :=
  harmonicBallNoveltyStmt_of_existence_and_results_canonical_derivedInputs47.{u}
    (harmonicBallNotMetricBallCanonical_of_localMetricReplacement_derived.{u} hN2)

end HarmonicBalls
