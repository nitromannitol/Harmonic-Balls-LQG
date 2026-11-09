import HarmonicBalls.Proposed.LQG

/-!
# First-pass frozen inputs for Proposition 11.9 (fp-S11d, owner n3)

FIRST-PASS FROZEN inputs for `firstPass_11_9` (paper `prop:mass-diam-gen`, corrected draft lines 3018-3137; repair in
`notes/fp-11-9-fix.md`). Each is a `def ... : Prop` (never an axiom). Reused, not re-frozen: `LQGMeasureWeylScaling`
(Proposed/LQG.lean, Fact 2.1 III) and `LQGMetricFieldAxioms` (Proposed/LQG.lean, Fact 2.2 I-IV for `h = h^ℂ - α₀ log|·|`,
including the Weyl identity III: `weylScaling (𝔇 (hC ω)) ξ (f - α₀ log) = weylScaling (D_h ω) ξ f`).
-/

namespace HarmonicBalls

open MeasureTheory
open scoped ENNReal

/-- FIRST-PASS FROZEN. Plane topology (standard; locator pending). For a connected open `V ⊆ ℂ` and a compact convex
`K ⊆ V`, the set `V \ K` is preconnected. Source: Alexander duality in `S²`: the Čech `H¹` of the complement of `V` and
of `K` vanish, so the complement of their union is connected (for `K` a closed dyadic square this is the connectedness
of `V \ S₂` used in the paper, proof of `prop:mass-diam-gen`, line 3120). Used by: firstPass_11_9. -/
def PlaneDomainMinusConvexCompactPreconnectedFrozen : Prop :=
  ∀ V K : Set ℂ, IsOpen V → IsConnected V → IsCompact K → Convex ℝ K → K ⊆ V → IsPreconnected (V \ K)

/-- FIRST-PASS FROZEN. Fact 2.2 I for the field `h + g = h^ℂ + g - α₀ log|·|` with `g` continuous: a.s. the Weyl-scaled
metric `e^{ξ g} · D_h` is finite and a length metric inducing the Euclidean topology. Source: Bou-Rabee-Gwynne
(arXiv:2208.11795) Fact 2.2 I (lines 432-457) applied to `h + f` as in Fact 2.2 III (line 445); Gwynne-Miller 2021
(`gwynne2021existence` in the paper bibliography; arXiv locator pending) Section 1.2 p. 6; Dubedat-Falconet-Gwynne-Pfeffer-Sun 2020 (arXiv:1905.00380)
Theorem 1.10 p. 10 and Proposition 3.17 p. 43 for the log singularity. Used by: firstPass_11_9. -/
def LQGMetricContinuousShiftFactI : Prop :=
  ∀ (γ ξ α₀ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
    ∀ g : ℂ → ℝ, Continuous g →
      ∀ᵐ ω ∂P, (∀ u v, weylScaling (𝔇 (hC ω)) ξ (fun x => g x - α₀ * Real.log ‖x‖) u v < ⊤) ∧
        IsEuclideanLengthMetric fun u v =>
          (weylScaling (𝔇 (hC ω)) ξ (fun x => g x - α₀ * Real.log ‖x‖) u v).toReal

/-- FIRST-PASS FROZEN. Fact 2.2 II (locality) for the field `h + g` with `g` continuous: for each deterministic open `U`,
the internal metric of the Weyl-scaled metric on `U` is a.s. equal to a function `G` that is measurable for the
pairing σ-algebra of `hC` on `U` (the σ-algebra of `h + g` on `U` equals that of `h` on `U`, since `g` is deterministic).
Source: Bou-Rabee-Gwynne (arXiv:2208.11795) Fact 2.2 II (line 441), applied to `h + f` (Fact 2.2 III, line 445);
Gwynne-Miller 2021 Section 1.2 p. 6 (locator pending). Used by: firstPass_11_9. -/
def LQGMetricContinuousShiftLocality : Prop :=
  ∀ (γ ξ α₀ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
    ∀ g : ℂ → ℝ, Continuous g → ∀ U : Set ℂ, IsOpen U →
      ∃ G : Ω → ℂ → ℂ → ℝ≥0∞, (∀ z w, Measurable[pairingSigmaAlgebra hC U] fun ω => G ω z w) ∧
        ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U,
          internalMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => g x - α₀ * Real.log ‖x‖) u v).toReal) U z w
            = G ω z w

end HarmonicBalls
