# Section 11 proper-metric geodesic conditional audit

**Scope and verdict.** The audited targets are the two helper theorems in
`HarmonicBalls/Steps/Sec11/MetricProperGeodesics.lean:19,41`, not frozen numbered
statements. Conditional composition: **PASS**, with the inputs below. Source
semantics/numbered closure: **OPEN**: the two staged propositions remain pending
operator source-check, the singular properness bridge is not proved, and the
conclusions are point-to-point paths. In particular this is not a Section 11
closure or an audit approving a frozen declaration.

`HarmonicBalls/Audit/Section11ProperGeodesics.lean` gives typed applications of
both targets with the complete bodies of the two staged propositions and the
singular representative expanded, and checks the deterministic export. It also
checks the individual fields of the bundled GFF, metric-map and length-metric
structures. `SatisfiesLQGMetricAxioms` is itself the four-field structure at
`Defs/LQGMetric.lean:146-160`; it contains length/topology, locality, Weyl scaling,
and coordinate change. Other mathematical objects used in their types (Gaussian
process, covariance, path length, Weyl scaling) are not re-proved by these tests.

## Source and scope

The corrected paper fixes `0 < γ < 2` and `α₀ < Q = 2/γ + γ/2`, with
`h = h^ℂ - α₀ log |·|` and normalized whole-plane `h^ℂ`, at lines 355-383.
Fact 2.2 I is length plus Euclidean topology (432-435); its exponent is
`ξ = γ/d_γ` (438-442). Lines 458-462 define geodesics between disjoint compact
sets and assert existence using a compactness argument and BBI Cor. 2.5.20.
Lemma 11.14 uses a geodesic from 0 to a compact set and one from 0 to z
(3160-3174, 3185-3187). The two exports instead prove a stronger pairwise
constant-speed distance identity for each *point pair*, with a `Path` continuous
in the Euclidean topology; they do not themselves construct a geodesic between
compact sets or a Lean equality of `pathLength` and endpoint distance.

[DFGPS, Lemma 3.8, p. 408](https://doi.org/10.1007/s00440-020-00979-6)
is stated for the unit-circle-normalized whole-plane GFF: every closed bounded
subset in its weak LQG metric is a.s. compact. The printed proof uses tightness
across scales and a scaling-exponent theorem, not merely Fact 2.2 I. The staged
`WholePlaneLQGMetricBoundedlyCompact` at `Proposed/MetricProperness.lean:26-32`
asks only for Euclidean compactness of every metric closed ball, simultaneously
in all centers and real radii, for each fixed metric map. This is the relevant
corollary if the Lean map and parameters meet the cited weak-metric hypotheses.
The source does not state the singular-field conclusion. Its admissibility as
an input and the metric identification are still subject to operator review.

## Expanded assumptions and use

`Ω`, its measurable space, `P`, `γ`, `ξ`, `α₀`, the field maps, and `D` or `𝔇`
are fixed before the hypotheses and almost-sure event. The following are
conditional helper assumptions, not a claim that they are premises of a numbered
result. The SOURCE/STANDING/TYPING/EXCESS labels below are relative to the
paper's asserted geodesic existence; no author ruling changes these assumptions.

| Expanded input | Classification and actual consumption |
| --- | --- |
| Measurable `Ω`, measure `P`, maps into `ℝ`/`ℂ` | TYPING. The singular theorem allows `Type u`; the whole-plane theorem requires `Type`, since the metric map's structure quantifies over `Type`. |
| `IsWholePlaneGFF P hC hcirc` | STANDING: normalized GFF; fields include measurable pairings/circle averages, joint Gaussian law, zero means, covariance, and a.s. joint circle-average continuity (`Defs/GFF.lean:93-109`). Passed to the metric-field or metric-map hypotheses and whole-plane properness. No standalone assumption that `P` is a probability measure is inserted. |
| `0 < γ`, `γ < 2` | STANDING, paper 373; used when applying staged inputs. |
| `α₀ < lqgQ γ` | STANDING, paper 373-383; singular theorem only. No lower bound on `α₀`. |
| `IsLQGMetric γ ξ 𝔇` | STANDING metric-map representation but semantic identification OPEN: measurable evaluations and axioms I–IV for every GFF plus random continuous shift (`Defs/LQGMetric.lean:179-185`). The whole-plane theorem consumes I at zero shift; the singular theorem obtains a witness from the representative. |
| Singular representative: `∃ 𝔇, IsLQGMetric γ ξ 𝔇 ∧ ∀ᵐ ω, ∀ u v, 0 ≤ D ω u v ∧ ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v` | STANDING representation, source scope subject to the staged field interpretation. `MetricField.lean:25-33` uses this very witness and the a.s. nonnegative identity to identify `D` with the finite Weyl-scaled length metric. |
| Singular `LQGMetricFieldAxioms` | EXCESS conditional input pending source-check. Expanded in the Lean example: after GFF, γ and α conditions, **every** `𝔇` satisfying `IsLQGMetric` has a.s. finite singular Weyl scaling and Euclidean length metric; locality for every open set; a.s. Weyl composition for every continuous function; and for each positive scale and translation an a.s. coordinate identity. Only the length-metric projection is used by this provider; its quantifiers are retained, not asserted proved. |
| Singular `∀ᵐ ω, ∀ x R, IsCompact {z : ℂ \| D ω x z ≤ R}` | EXCESS explicit missing premise. Consumed directly at `MetricProperGeodesics.lean:29-37`; there is no whole-plane properness premise or derivation in that theorem. |
| Whole-plane `IsWholePlaneGFF → 0 < γ → γ < 2 → ∀ 𝔇', IsLQGMetric γ ξ 𝔇' → ∀ᵐ ω, ∀ z R, IsCompact {w \| 𝔇' (hC ω) z w ≤ R}` | EXCESS staged input pending source-check. Consumed at `MetricProperGeodesics.lean:57`, for the given `𝔇`; does not mention the logarithmic field. |

Each `∀ᵐ ω` in the conclusions precedes `∀ x y`, so one event works for all
point pairs. Both staged propositions quantify over the metric map before the
a.s. event, not one common event over all metric maps. Each uses an arbitrary
fixed real `ξ`; neither theorem has an explicit `ξ > 0` or
`ξ = γ/d_γ` hypothesis, nor defines `d_γ`. An `IsLQGMetric γ ξ 𝔇` witness is
required, but the code has not identified this axiomatic condition with the
source's physical exponent/weak metric; do not treat such identification as
proved. `α₀` in the singular theorem is fixed arbitrarily subject only to
`α₀ < Q`, and is absent from the whole-plane theorem. For a numbered-result
binder audit, these conditional EXCESS premises would prevent a passing source
statement; this table is not a five-bin count for a frozen declaration.

## Deterministic dependency trace

`ProperMetricIntermediate.lean:38-54` uses compact closed balls to minimize a
distance and construct intermediate points. Its finite subdivisions feed
`ProperMetricDyadic.lean:18-34,64-66`, which uses compactness of a countable
product to extract a common subsequence. `ProperMetricExtension.lean:17-68`
uses compactness again to extend the dyadic map; lines 86-138 give an isometric
interval map and lines 142-164 turn it into a Euclidean-continuous `Path`.
`MetricProperGeodesics.lean:31-37,58-64` derives nonnegativity from symmetry,
triangle inequality and vanishing diagonal, and supplies it and compactness to
that deterministic export. No properness follows from length/topology alone;
E36 records a slit-plane counterexample to that implication.

A repository text search finds no downstream references to either named
geodesic export beyond its definition. The actual current conditional Lemma
11.14 provider `Proofs/Sec11/PinchMetricBall.lean:20-44` uses `MetricField`
and the inner/outer inclusions, where `PinchInner.lean:37` and
`PinchOuter.lean:46` take almost-minimizing paths. It does not use either
geodesic export or compact-ball hypothesis. This observation does not settle
its own staged metric-field source check or other Section 11 inputs.

## Unresolved singular-field bridge (E36)

The following precise **derived obligation**, already recorded in
`~/paper-fleets/hb/INPUT-REQUESTS.md`, is not proved or admitted here:

```lean
∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
  (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
  (D : Ω → ℂ → ℂ → ℝ),
  WholePlaneLQGMetricBoundedlyCompact P γ ξ hC hcirc →
  LQGMetricFieldAxioms P γ ξ α₀ hC hcirc →
  IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ →
  IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ᵐ ω ∂P, ∀ z : ℂ, ∀ R : ℝ, IsCompact {w : ℂ | D ω z w ≤ R}
```

This is an obligation with the existing broad exponent assumptions, not a
claim that these assumptions suffice. Singular Weyl weights may shrink lengths
at infinity, so local equivalence and whole-plane bounded compactness alone do
not supply the bridge. E36, the exponent identification, and existing Section 11
moment/source requests remain open.

## Mechanical checks

The audit module passes `~/paper-fleets/hb/lc` and `~/paper-fleets/hb/lb`.
`#print axioms` for the deterministic export and both conditional targets
reports exactly `[propext, Classical.choice, Quot.sound]` for each. No
`sorry`, `admit`, `axiom`, or `native_decide` is introduced in the audit module.
These checks establish elaboration and conditional consumption, not source
approval of a staged input or validity of a numbered statement.
