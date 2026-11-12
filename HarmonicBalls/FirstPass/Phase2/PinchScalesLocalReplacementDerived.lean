import HarmonicBalls.FirstPass.Phase2.PinchScalesSeedInputsDerived
import HarmonicBalls.FirstPass.Phase2.RootedInsertionContinuityDerived

/-!
# Lemma 11.13 and Proposition 11.11 (canonical exponent) from the local metric replacement alone

The continuity of the rooted physical metric at the insertion (`RootedPhysicalMetricContinuousAtInsertionFrozen`,
Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, Proposition 3.17) is proved
(`rootedPhysicalMetricContinuousAtInsertion_derived`). Supplying it, Lemma 11.13 and Proposition 11.11 at the canonical
exponent `ξ = γ / d_γ` hold at every universe from the local metric replacement (`LocalMetricReplacementStmt`) alone.
-/

namespace HarmonicBalls

universe u

/-- **Lemma 11.13 (canonical exponent, every universe), derived** from the local metric replacement `hN2` alone. -/
theorem correctedLemma11_13Canonical_of_localMetricReplacement_derived
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂) :
    CorrectedLemma11_13CanonicalStmt.{u} :=
  correctedLemma11_13Canonical_of_seedInputs_derived hN2 rootedPhysicalMetricContinuousAtInsertion_derived.{0}

/-- **Proposition 11.11 (canonical exponent, every universe), derived** from the local metric replacement `hN2` alone,
through Lemma 11.13 and the field axioms. -/
theorem harmonicBallNotMetricBallCanonical_of_localMetricReplacement_derived
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂) :
    HarmonicBallNotMetricBallCanonicalStmt.{u} :=
  harmonicBallNotMetricBallCanonical_of_seedInputs_derived hN2 rootedPhysicalMetricContinuousAtInsertion_derived.{0}

end HarmonicBalls
