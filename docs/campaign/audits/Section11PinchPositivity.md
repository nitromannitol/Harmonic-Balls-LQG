# Section 11 constrained positivity: conditional audit

Scope: `Draft/Section11.lean:246,289–324`, corrected TeX 3100–3137 and
3236–3297. Frozen inventory: `docs/campaign/FROZEN.md:85,88–90`.
C11 is the frozen reading of 11.12 listed there; the TeX at 3137 still
prints the cone-event symbol. The source's keyhole figure is not fully
encoded; `Draft/Section11.lean:43–51` makes this explicit. No numbered
result is closed by this audit. C17 concerns the rooted use of 11.12 and
is not a proof of positivity at the insertion.

## Frozen binder inventory and source comparison

In each row below, the sets are fixed *before* γ, ξ, probability space,
measure, metric and (when present) M. All four have `α₀ = 0`.

| Declaration | Existential binders | Universal binders, in order | Assumptions and conclusion |
|---|---|---|---|
| 11.12 | `U T Q' Q`, pinch configuration | `γ ξ`, `Ω [MeasurableSpace Ω] P hC hcirc μ D`, then `M` | `0 < γ < 2`, GFF, LQG measure and metric; `M > 0`; measurable positive subset of `pinchPointEvent` |
| 11.15 | `U V W T Q' Q δ`, proof configuration | `γ ξ`, `Ω [MeasurableSpace Ω] P hC hcirc D` | `0 < γ < 2`, GFF and metric; measurable positive subset of E₁ |
| 11.16 | same proof configuration | `γ ξ`, `Ω [MeasurableSpace Ω] P hC hcirc μ D`, then `M` | same field assumptions as 11.12, `M > 0`; measurable positive subset of E₁ ∩ E₂(M) |
| 11.17 | same proof configuration | same as 11.16 | same as 11.16; measurable positive subset of E₁ ∩ E₂(M) ∩ E₃ |

The types/carriers are ℂ sets, real parameters, `P : Measure Ω`,
`hC : Ω → (ℂ → ℝ) → ℝ`, `hcirc : Ω → ℝ → ℂ → ℝ`,
`μ : Ω → Measure ℂ`, `D : Ω → ℂ → ℂ → ℝ`. No `0 < ξ` binder
occurs in any frozen target. The GFF structure has six fields
(`Defs/GFF.lean:93–110`): pairing and circle measurability, joint Gaussian
law, mean, covariance and circle-average continuity. `IsLQGMeasureOfField`
expands to a.s. local finiteness plus dyadic vague convergence
(`Defs/LQG.lean:52–75`). `IsLQGMetricOfField` expands to existence of a
measurable metric functional satisfying the whole-plane four axioms and
a.s. nonnegative singular Weyl representation (`Defs/LQGMetric.lean:163–207`).
Their full source semantics and individual five-bin binder counts are not
certified by this scoped audit; these are standing modeling assumptions,
not evidence of the desired event. `IsPinchPointProofConfiguration`
expands to the 15 base geometry fields (`Defs/Geometry.lean:190–205`)
plus the 13 fields in `Draft/Section11.lean:125–138`. The visible
requirements do not determine the depicted keyhole shape. Source/semantic
verdict: **not approved**, pending full definition, source and dependency
audit, including physical ξ and the keyhole encoding.

## Actual producer consumption

`Audit/Section11PinchPositivity.lean` gives exact, fully applied calls to
`positive_singular_internal_pinch_of_canonicalLaw` at general α and at
α = γ, and to `positive_singular_internal_pinch_of_radial_product`, with
all their outer arguments expanded. The α = γ call consumes
`gamma_lt_lqgQ` (`Steps/Sec11/ScalePowerBounds.lean:43`), but still assumes
both the common buffered event and the joint law. It does not deduce
positive probability from γ < Q. The Lean file also checks that 11.17
implies 11.16 with the identical configuration and measurable witness;
it does not prove 11.17. A second fixed-parameter example projects a
buffered event to E₁ ∩ E₂ only in outer measure. In particular, it does
not establish 11.15, whose input has no μ, or supply a measurable subset.

Canonical law (`BufferedPinchCanonicalLaw.lean:15–48`) requires `0 < ξ`,
`0 < q ≤ 1`, the staged `LQGMetricFieldAxioms`, a measurable joint random
pair X with a.e. equality to the actual μ and D, and for every supported
nonpositive smooth shift a joint shifted Y, a.e. geometric identities and
`P.map Y ≪ P.map X`. Its `hA` is positive *outer* measure of the
intersection E₁, E₂ and three additional inequalities: a common radial
barrier, strict obstacle-avoiding path bound `< q b`, and strict
`q * internalDiam < sphere gap`. The conclusion is positive outer measure
of the strengthened internal-bound event, not the frozen measurable-subset
conclusion. `InternalPinchScales.lean:30–44` converts this pointwise to the
original event on a length metric; an a.e. metric and measurable-subset
extraction are still needed for the frozen statement.

`PinchBufferCompatibility.lean:41–57,79–118` proves the exact arithmetic
criterion for common q: `L < b` and `L*C < b*H`, for finite nonnegative
quantities and positive b,H, and selects deterministic q,b if that entire
product-gap event together with E₁ and E₂ has positive mass. It does not
prove that positivity. Independent positivity of separate events is
insufficient to infer positivity of their intersection. The alternative
`PinchRadialProductShift.lean:18–51` uses that product-gap event and a
quasi-measure-preserving sample-space shift with both circle-average and
metric identities; it proves only strengthened outer positivity. The
whole-plane third-event producer `WholePlanePinchThirdEvent.lean:18–35`
gives a shifted E₃ on part of a positive event; its own docstring says no
change-of-law transfer, and it does not assert preservation of E₁ and E₂.
`PinchProofAssembly.lean:17–36` consumes all three events *and* a strict
path bound inside B₆; `PinchConstrainedWitness.lean:16–52` translates that
bound into uniform paths, without proving their positive probability.
`PinchGreenFinite.lean:50–81` supplies Green finiteness/thresholds only
conditionally on volume growth, existing positive event, and a.e. metric.

## Decoder scope and unresolved leaves

`JointSingularWeylShift.lean:23–72` (commit a47cca2) combines normalized
singular measure and countably many normalized internal distances under
smooth nonpositive shifts, with both law directions. It assumes full
support, a base metric functional, singular Weyl representation, staged
metric field axioms, a test normalizer, open domains with a **common**
positive lower bound on distance to 0, and first endpoint in each domain.
The output is a *normalized restriction* of μ and normalized internal
distances, not the full canonical pair X,Y and equalities required above.
`SingularWeylExhaustion.lean:19–50,80–114` (commit ee6ee6b) gives a
pointwise a.e. infimum formula for increasing separated exhaustions and
then `U \ {0}`. It neither identifies distances through 0 nor itself
constructs the full joint canonical observable for that limit. The target
uses 0 as an endpoint, so passage through the insertion is substantive.
Any uncommitted provider file is excluded from this committed-snapshot audit.

The explicit remaining leaves are the exact `hA` and `hshiftLaw` types in
`BufferedPinchCanonicalLaw.lean:29–44`, including at α = γ; uniform
configuration choice; the a.e.-length and measurable-subset bridge to the
frozen inner-measure statement; and a separate first-event positive
producer. Positive internal-diameter moments and the admissible physical
`ξ = γ / dγ` identification remain pending: see fleet
`INPUT-REQUESTS.md:190–206` and 250–264; DFGPS Theorem 1.8 p.378 is a
candidate source under review, not an admitted input. Rooted/Palm transfer
and stationarity are additional obligations for 11.13, not consequences
of α = 0 positivity. E36 records that length plus Euclidean topology does
not alone supply properness/geodesics; E44 records missing strict E₂
margins; E45 records the larger-diameter inclusion issue; E47 gives the
numerical contraction error. These are proof gaps, not counterexamples to
the frozen lemmas. Proposed literature Props remain hypotheses pending
operator source check.

Conditional-composition verdict: the explicit applications and implications
checked here are valid under their displayed premises; no producer inspected
establishes the missing common positivity or the full canonical singular
shift law. Source/semantic verdict: **open**, no numbered closure.
