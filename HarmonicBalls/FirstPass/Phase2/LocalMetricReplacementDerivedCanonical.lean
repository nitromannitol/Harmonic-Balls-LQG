import HarmonicBalls.FirstPass.Phase2.LocalMetricReplacementR4Derived
import HarmonicBalls.FirstPass.Phase2.NoveltyCanonicalLocalReplacementDerived

/-!
# The canonical-exponent forms of Lemma 11.13, Proposition 11.11 and Theorem 1.2 without hypotheses

The local metric replacement `LocalMetricReplacementStmt` holds for every `γ ∈ (0, 2)`, every `ξ > 0` and every pair of
discs (`localMetricReplacementStmt_derived`). Supplying it to the derived forms that take it as their only hypothesis,
Lemma 11.13, Proposition 11.11 and Theorem 1.2 at the canonical exponent `ξ = γ / d_γ` hold at every universe with no
hypothesis left.
-/

namespace HarmonicBalls

universe u

/-- The local metric replacement for all parameters, in the binder shape of the derived canonical forms. -/
theorem localMetricReplacement_all_derived :
    ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂ :=
  fun γ ξ _ _ _ c₁ c₂ r₁ r₂ => localMetricReplacementStmt_derived.{0} γ ξ c₁ c₂ r₁ r₂

/-- **Lemma 11.13 (canonical exponent, every universe)** without hypotheses. -/
theorem correctedLemma11_13Canonical_derived : CorrectedLemma11_13CanonicalStmt.{u} :=
  correctedLemma11_13Canonical_of_localMetricReplacement_derived.{u} localMetricReplacement_all_derived

/-- **Proposition 11.11 (canonical exponent, every universe)** without hypotheses. -/
theorem harmonicBallNotMetricBallCanonical_derived : HarmonicBallNotMetricBallCanonicalStmt.{u} :=
  harmonicBallNotMetricBallCanonical_of_localMetricReplacement_derived.{u} localMetricReplacement_all_derived

/-- **Theorem 1.2 (canonical exponent, every universe)** without hypotheses. -/
theorem harmonicBallNoveltyCanonical_derived : HarmonicBallNoveltyCanonicalStmt.{u} :=
  harmonicBallNoveltyCanonical_of_localMetricReplacement_derived.{u} localMetricReplacement_all_derived

end HarmonicBalls
