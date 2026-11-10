import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# First-pass frozen input: the marked rooting identity (fp-S11r, owner n2)

One EXTERNAL identity for the rooted (Campbell-Palm) law of the LQG measure of a whole-plane GFF, used in
the proof of the local metric replacement (CHATGPT-n3-B1-B2.md, section 4.2, equation (24), marked form).
The second input of section 4.2, the measurable metric decoder, is already frozen as
`LQGCanonicalDecodersMeasurableExistStmt` (`FirstPass/Frozen/S11n.lean`) and is reused, not restated.
A `def ... : Prop`, never an axiom.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

universe u

/-- FIRST-PASS FROZEN, EXTERNAL. The marked rooting identity for the LQG measure `μ_h` of
`h = h^ℂ - α₀ log|·|` (Duplantier-Miller-Sheffield, arXiv:1409.7055v4, Lemma A.10, marked form, printed p. 184,
proof pp. 184-185; Duplantier-Sheffield, arXiv:0808.1560v2, Proposition 1.1 for the LQG measure). For disks
`U = ball c₁ r₁` with `closedBall c₁ r₁ ⊆ D = ball c₂ r₂` and `0 ∉ closedBall c₂ r₂`, and every Borel set `S` of
marked observations `(z, obs_D)`, the mass-weighted marked law equals the Lebesgue mixture of the reference laws:
`E[∫_U 1_S(z, obs_D h) μ_h(dz)] = ∫_U E[1_S(z, obs_D f_z)] dz`, where `f_z = g - γ log|·-z| + b` is the rooted field
(`campbellReferenceObs`) and `obs_D h` is the marked observation (`campbellMarkedObs`). Taking `S = ℂ × A` gives
the unmarked identity (24): `∫_U P[obs_D f_z ∈ A] dz = E[μ_h(U) 1{obs_D h ∈ A}]`.

This is an EQUALITY of unnormalised measures. The one-sided statement `LocalCampbellMarkedRestrictionFrozen`
(Frozen/S11c.lean) only transfers null sets from the reference mixture to the normalised Campbell law, and does
not give this equality; this is why the answer names the marked identity as a separate input.
PENDING TRUTH CHECK (operator to route): the normalisation of `μ_h` (`IsLQGMeasureOfField`) and the shift `b`
must match the source exactly; not yet checked. -/
def LocalMarkedRootingIdentityFrozen : Prop :=
  ∀ (γ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
  IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), 0 < r₁ → 0 < r₂ → closedBall c₁ r₁ ⊆ ball c₂ r₂ → (0 : ℂ) ∉ closedBall c₂ r₂ →
  ∀ S : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)), MeasurableSet S →
    (∫⁻ ω, ∫⁻ z in ball c₁ r₁,
        S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω) ∂P)
      = ∫⁻ z in ball c₁ r₁,
        (∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P)

end HarmonicBalls
