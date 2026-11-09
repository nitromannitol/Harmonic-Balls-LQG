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

/-- FIRST-PASS FROZEN. Cameron-Martin quasi-invariance of the whole-plane GFF on distribution-level events (standard;
locator: Miller-Sheffield Imaginary Geometry, Proposition 2.9 (paper line 3106 cites it as miller2017imaginary) for the Cameron-Martin shift
`h ↦ h + g` with `g` in the Cameron-Martin space; the whole-plane GFF normalised by its unit-circle average, so the shift
must have zero unit-circle average). For smooth (`C^∞`, so in the Dirichlet/Cameron-Martin space) compactly supported `g` with zero unit-circle average, the laws of `hC`
and `hC + g` on the distribution σ-algebra are mutually absolutely continuous: a measurable set of fields is null for
`hC` iff it is null for `hC + g`. Used by: firstPass_11_9 (transfer of the positive-probability event from the shifted field
`h~ = h - (φ/ξ) log(2A/ε)` back to `h`, paper line 3131, "since the laws of h and h~ are mutually absolutely continuous"). -/
def CameronMartinGFFMutualAbsCont : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (g : ℂ → ℝ), IsWholePlaneGFF P hC hcirc → ContDiff ℝ (⊤ : ℕ∞) g →
    HasCompactSupport g → Real.circleAverage g 0 1 = 0 →
    ∀ B : Set ((ℂ → ℝ) → ℝ), MeasurableSet[distributionMeasurableSpace] B →
      (P ((fun ω => hC ω) ⁻¹' B) = 0 ↔ P ((fun ω => addFunPairing (hC ω) g) ⁻¹' B) = 0)

/-- FIRST-PASS FROZEN. Composition rule of Weyl scalings for the log-singular LQG metric (paper Fact 2.2 III, line 445:
`D_{h+f} = e^{ξ f} · D_h` for continuous `f`, applied with `h = h^ℂ - α₀ log|·|`; Gwynne-Miller 2021, Section 1.2 p. 6 and
Remark 1.5 p. 8; Dubedat-Falconet-Gwynne-Pfeffer-Sun 2020, p. 9). It identifies the metric of the distribution `h^ℂ + g - α₀ log|·|`
(the Defs convention `weylScaling (𝔇 ·) ξ (-α₀ log|·|)`) with the Weyl scaling of the metric of `h`, almost surely.
Used by: firstPass_11_9 (the Weyl comparison `internalMetric_weylScaling_le` for the shifted metric, paper line 3127). -/
def WeylScalingCompositionFrozen : Prop :=
  ∀ (γ ξ α₀ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
    ∀ g : ℂ → ℝ, Continuous g →
      ∀ᵐ ω ∂P, ∀ x y : ℂ,
        weylScaling (𝔇 (addFunPairing (hC ω) g)) ξ (fun z => -α₀ * Real.log ‖z‖) x y =
          weylScaling (𝔇 (hC ω)) ξ (fun z => g z - α₀ * Real.log ‖z‖) x y

end HarmonicBalls
