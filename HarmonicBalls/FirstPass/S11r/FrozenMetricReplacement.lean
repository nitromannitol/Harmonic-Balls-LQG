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

/-- RETIRED (FALSE, ChatGPT 01:48 UTC; CHATGPT-n2-frozen-S11r.md section 2.1): the unweighted Lebesgue mixture over the
root has the wrong total mass. Superseded by `LocalMarkedRootingIdentityWeightedFrozen` below; do not use. The text below
is the retired statement.

FIRST-PASS FROZEN, EXTERNAL. The marked rooting identity for the LQG measure `μ_h` of
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
Retired (truth check FALSE, ChatGPT 01:48 UTC, section 2.1: wrong total mass); the replacement is
`LocalMarkedRootingIdentityWeightedFrozen`. -/
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

/-- The root density `q_{γ,α₀}(z) = |z|^{-γ α₀} · max(1, |z|)^{γ²}` of the corrected marked rooting identity
(CHATGPT-n2-frozen-S11r.md section 2.4), as `exp` of a real number: a positive value in `ℝ≥0∞` for every root `z`. -/
noncomputable def rootWeight (γ α₀ : ℝ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-γ * α₀ * Real.log ‖z‖ + γ ^ 2 * Real.log (max ‖z‖ 1)))

/-- FIRST-PASS FROZEN, EXTERNAL. Truth check TRUE (ChatGPT, 02:49 UTC; notes/fp-gaps/CHATGPT-n2-frozen-corrected.md
section 2). The marked rooting identity with the root density
(CHATGPT-n2-frozen-S11r.md section 2.4, equation (9): the minimal correction of the retired `LocalMarkedRootingIdentityFrozen`,
retaining the current scope of arbitrary disks away from zero). For `h = h^ℂ - α₀ log|·|` with
`IsLQGMeasureOfField P γ α₀ hcirc μ`, disks `U = ball c₁ r₁` and `D = ball c₂ r₂` with `closedBall c₁ r₁ ⊆ D`,
`0 ∉ closedBall c₂ r₂`, and every measurable set `S` of marked observations `(z, obs_D)`,
`E[∫_U 1_S(z, obs_D h) μ_h(dz)] = ∫_U q_{γ,α₀}(z) · E[1_S(R_D(g, z))] dz`, where `q_{γ,α₀} = rootWeight γ α₀` and
`R_D(g, z) = campbellReferenceObs γ α₀ D (hC ω) z` is the reference observation (equation (8): `obs_D g` with the
logarithmic insertion `-γ log|· - z| + γ log max(1, |·|)`, which `campbellReferenceObs` implements). The integrals are
lower Lebesgue integrals. Measurability: the observation maps are jointly measurable by `IsWholePlaneGFF.measurable_pairing`
and continuity of the deterministic root-shift pairings; the specified LQG measure agrees almost surely with a measurable
random-measure version (continuous circle-average profile and its dyadic vague limit), so no extra measurability hypothesis
is needed for the displayed lower-integral identity (section 2.5 of the answer). Sources: Duplantier-Miller-Sheffield,
arXiv:1409.7055v4, Lemma A.10, printed p. 184, proof pp. 184-185 (marked form; the arbitrary-disk density is obtained by
the Gaussian-tilting computation there, not printed verbatim); Duplantier-Sheffield, arXiv:0808.1560v2, §3.3 printed pp. 22-23,
especially (25) p. 22 (marked pair, root marginal, conditional Gaussian shift); Propositions 1.1-1.2 p. 5 are not the source of
the marked equality. Conventions: HB arXiv:2208.11795v3 (2.1) p. 8, (2.4), (2.6) p. 9; application Lemma 11.13 and (11.29) p. 59. -/
def LocalMarkedRootingIdentityWeightedFrozen : Prop :=
  ∀ (γ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
  IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), 0 < r₁ → 0 < r₂ → closedBall c₁ r₁ ⊆ ball c₂ r₂ → (0 : ℂ) ∉ closedBall c₂ r₂ →
  ∀ S : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)), MeasurableSet S →
    (∫⁻ ω, ∫⁻ z in ball c₁ r₁,
        S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω) ∂P)
      = ∫⁻ z in ball c₁ r₁,
        rootWeight γ α₀ z *
          (∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞))
            (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P)

end HarmonicBalls
