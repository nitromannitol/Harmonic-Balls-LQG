# Section 10 conditional crossing export audit

2026-11-05. **Conditional Lean composition: PASS. Source/semantic seal: NOT
ESTABLISHED.** Neither provider proves the paper's unconditional Lemma 10.1:
their explicit hypotheses remain to be supplied and source-checked. This audit
does not approve the staged inputs or close a numbered result.

## Pin and independent source reconstruction

* Frozen target: `HarmonicBalls.ClusterBoundedCrossingsStmt.{u}` is a `def :
  Prop`, `Draft/Section10.lean:57-63`; `FROZEN.md:73`, inventory row 10.1,
  `GRAPH.md:802-818`. Its whole-file SHA-256 is
  `275309fd7bddd433689c4c10ec2034f7f81ec7d54c84fdb562e6d9b7a03db481`.
  `FROZEN.md` records no declaration-specific byte hash or theorem-seal state;
  therefore a manifest-hash or approved proof-body-only seal cannot be verified.
* Source `paper/lqg_harmonic_ball-corrected.tex:2496-2502`, proof 2504-2544;
  source setup 355-396; Proposition 6.2 at 1078-1081. Both source files currently
  hash to `8fdbb03043011800560e4d947eb79a3cfdd7cc8767a3af94469f04201b7593fc`.
  This is E49 (`~/paper-fleets/hb/ESCALATIONS.md:345`): the corrected artifact
  does not contain the approved corrections. In particular the consumed
  Section 6 good-annulus event differs from uncorrected TeX 1119-1121 under C23.
  The source reconciliation remains open.
* Source order: for a fixed subcritical γ choose deterministic α(γ) ∈ (0,1),
  as in Proposition 6.2; a.s., eventually for every ε > 0, every
  `w ∈ B₁ \ B_{20√ε}` admits `ρ ∈ [ε,√ε]`, chosen before all `t > 0` and
  `z ∈ ℂ`. If `closure Λ_t(z) ⊆ B₁`, at most `⌈1/α⌉` components of
  `Λ_t(z) ∩ B_{2ρ}(w)` have closures meeting both specified circles. The
  probability setting is `h = h^ℂ - α₀ log |·|`, `α₀ < Q`. E22, operator
  inbox 2026-11-03 04:35, says keep the α₀-uniform statement as printed and
  prove it by localization; E31 at 04:45 fixes the relevant Section 6 order.
* `cluster` is the unit-disc least-supersolution cluster; `Defs/Obstacle.lean:51-71`
  contains its definition, the off-pole obstacle constraint, real-valued
  `sInf`, and explicit pole inclusion. `connectedComponentsIn` is the image
  of `connectedComponentIn` on the set and `crossingComponents` selects
  closures meeting both spheres (`Defs/Geometry.lean:113-125`). The typed
  conclusion check expands both crossing predicates. These are surface checks;
  a full audit of the Green function, least-supersolution construction, and
  the standing GFF/LQG definitions is not implied.

## Frozen binder classification

Counts are for the following explicit binder groups, including expanded
logical premises. SOURCE is read from the paper and standing setup; TYPING
is Lean realization data; RULED is an operator ruling. No proposed input is
part of the frozen proposition itself.

| Binder group in outer-to-inner order | Bin | Evidence and scope |
| --- | --- | --- |
| `γ : ℝ`, `0 < γ`, `γ < 2` | SOURCE | TeX 355-396, subcritical setting |
| `∃ α : ℝ`, `α ∈ (0,1)` | SOURCE | TeX 2499; constant chosen after γ |
| `∀ α₀ : ℝ`, `α₀ < Q` | RULED | E22/E31: after α, uniformly over α₀ |
| `Ω : Type u`, `[MeasurableSpace Ω]`, `P : Measure Ω` | TYPING | arbitrary realization of probability space; probability is contained in the GFF hypothesis |
| `hC`, `hcirc`, `μ` | TYPING | observables `Ω → (ℂ → ℝ) → ℝ`, `Ω → ℝ → ℂ → ℝ`, and `Ω → Measure ℂ` |
| `IsWholePlaneGFF P hC hcirc` | STANDING | TeX 355-380; structure fields at `Defs/GFF.lean:93-109` |
| `IsLQGMeasureOfField P γ α₀ hcirc μ` | STANDING | TeX 390-396; dyadic vague-limit interface `Defs/LQG.lean:48-74` |
| `∀ᵐ ω ∂P` | SOURCE | TeX 2496 |
| `∀ᶠ ε in 𝓝[>] 0` | SOURCE | all sufficiently small positive ε |
| `∀ w ∈ B₁ \ B_{20√ε}` | SOURCE | TeX 2496-2497; open ball is removed |
| `∃ ρ ∈ [ε,√ε]` | SOURCE | TeX 2497; ρ may depend on ω, ε, w |
| `∀ t : ℝ`, `0 < t`, `∀ z : ℂ` | SOURCE | TeX 2498; after ρ, including outside-disc poles |
| `closure (cluster ...) ⊆ B₁` | SOURCE | TeX 2498; compact containment reading `Draft/Section10.lean:30` |

Counts: SOURCE 8, STANDING 2, TYPING 2, RULED 1, EXCESS 0 (13 groups).
The conclusion has `Set.encard ≤ ⌈1 / α⌉₊`; positive α ensures the natural
ceiling agrees with the printed integer ceiling. The extra provider premises
below are **EXCESS for unconditional Lemma 10.1**, not binders of this frozen
statement. A compiled conditional implication does not discharge them.

**Source discrepancy requiring operator review:** TeX 2499 specifies the same
α as Proposition 6.2. The frozen docstring `Draft/Section10.lean:54-56`
explicitly records this only in prose; the proposition merely asserts some α.
The actual route chooses its α via `prevalent_displaced_crossing_events`
(`PrevalentPoleAvoidingCrossings.lean:15-49`) rather than consuming a specified
6.2 witness. Thus the checked proposition does not itself encode the printed
identity; no assertion of falsity or permission to change the frozen file is
implied. A proof that the chosen α can serve both results, or an authorized
reading that the identity is immaterial, is needed for a complete source seal.
The independently raised Section 6 scope issue also persists:
`Draft/Section6.lean:311-321` places arbitrary βminus before the a, C and N
witnesses, while TeX 1297 states their dependence on b, γ (and a for C);
E31 settles α₀ order, not this βminus question. See
`Section6ConditionalExports.md` for the precise interpretation and evidence.

## Exact conditional premises and use

`Audit/Section10CrossingExports.lean:22-76` gives explicit Lean types with the
project proposition aliases for all provider hypotheses expanded:

* `clusterBoundedCrossings_of_volumeGrowth_and_zero_existence` consumes I2,
  including all γ, α₀, realization, a.s. R, exponent and ball quantifiers,
  and the zero-strength LQG existence proposition. I2 is a derived project
  statement (`Draft/Section2.lean:122-130`), not a source-approved input.
  E0 is `Proposed/LQG.lean:64-66`, existence of the dyadic limit for every
  realization satisfying the GFF and subcritical hypotheses.
* `clusterBoundedCrossings_of_three_staged_inputs` consumes precisely:
  `WholePlaneLQGBallMassBounds` (Ding–Gwynne, 2020, Lemma 3.8, p. 25;
  `Proposed/LQG.lean:146-151`); `LQGMeasureCoordChange` at α₀ = 0
  (Duplantier–Sheffield 2011, Prop. 2.1, p. 13; Sheffield–Wang 2016,
  Thms. 1.1 and 1.4, p. 3; `Proposed/LQG.lean:108-112`); and
  `LQGMeasureExistence` for all subcritical singularity strengths
  (Duplantier–Sheffield 2011, Prop. 1.1, p. 5; Berestycki–Powell,
  Thm. 2.1, p. 62; `Proposed/LQG.lean:64-66`). All three are **pending
  operator source-check**. The example expands `PolyHighProb` into real
  exponent and outer-measure tail bounds. The strong simultaneous affine
  coordinate change and global on-space existence deserve the pending check.
* The source setup, `IsWholePlaneGFF` and `IsLQGMeasureOfField`, are still
  bundled predicates, not independently source-certified by these examples.
  The examples expose every top-level conditional premise; the full recursive
  semantic audit of those standing predicates is outstanding.

The three-input provider applies `lqgVolumeGrowthAllScalesStmt_of_existence`
(`Proofs/Sec9/ExistenceResultsAssembly.lean:36-49`) and specializes hE at zero.
That producer uses rescaled Ding–Gwynne, proved affine invariance, hCC,
proved Weyl scaling and zero existence, and derives non-atomicity from
existence at a stronger subcritical singularity. It then uses the two-input
provider (`PrevalenceCrossingAssembly.lean:19-39`).

## Actual crossing dependency path

1. `clusterBoundedCrossings_of_volumeGrowth_and_zero_existence` obtains 6.6
   from `Section6.manyVeryGoodAnnuliStmt_of_volumeGrowth_zero_existence`
   (`SevenAdicFineSupportPrevalence.lean:112-122`). This uses
   `veryGoodAnnuliSubRangeStep_of_volumeGrowth_fineSupport`, derived from
   seven-adic good-annulus probability and I2, then singular-weight transfer
   with E0 and proved Weyl scaling (`Proofs/Sec6/Prevalence.lean:162-170`).
   The imported iteration uses Leonardo Bonanno's
   `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6` and field-law bridges
   `LatticeProb.Bonanno.LQGMetric.Field.GFFLaw`, `.CircleAvgRate`, `.ExistGFF`.
   The Section 6 audit describes the deeper chain and its limitations.
2. `DyadicCrossingAssembly.lean:121-125` supplies 6.9 from I2 by
   `Section6.odometerHarmonicMeasureBoundStmt_of_volumeGrowth`
   (`PlanarBrownianGenerator.lean:60-63`), then combines 6.6, 6.9 and I2.
   No final crossing conclusion is supplied as a top-level premise.
3. `prevalent_displaced_crossing_events` derives a uniform α via 6.6 and
   `exists_ae_crossing_thresholds_independent_exponent`
   (`UniformCrossingComparison.lean:16-64`); it fixes β = (2+γ)²/2+1,
   then b, a, the C's and N₀ before α₀. Its comparison is *constructed* from
   6.9, volume growth and local finiteness. The geometric intermediate
   `exists_pole_avoiding_crossing_thresholds_independent_exponent`
   (`IndependentGrowthExponent.lean:205-241`) assumes a one-good-annulus
   **decay** estimate for pole-avoiding local components, plus very-good
   annulus criteria; that is a genuine intermediate analytic premise, not a
   verbatim 10.1 or 10.5 statement, and it is supplied by
   `component_goodAnnulus_decay_of_punctured_comparison`
   (`PoleAvoidingAnnulusComparison.lean:109`), itself using the 6.9 comparison.
   The sharp counting step `StrictMassCrossings.lean:170-204` handles an
   exceptional component containing the pole.
4. `PrevalentCrossingRadii.lean:14-108` uses Borel–Cantelli and at least three
   good eighth-power radii; `DoubleEndpointSelection.lean:32-82` removes at
   most one at each end to select ρ in `[2ε,√ε]` for every sufficiently small
   real ε, not just dyadic ε. The bound there has a boundary margin.
5. `DyadicCrossingAssembly.lean:17-77` pulls back by factor 2, applies the
   same estimate at ε/4, and uses positive time rescaling plus cluster
   compatibility to remove the boundary margin. The field transformation
   comes from `IsWholePlaneGFF.complex_affine`; the LQG pullback is proved
   directly for dyadic scaling (`LQGSpatialDilation.lean:107-150`), so this
   crossing step does not assume an additional coordinate-change premise.
   The factor-2 rescaling gives the final radius interval `[ε,√ε]`.
6. `DyadicCrossingAssembly.lean:80-117` handles poles outside B₁ using
   `cluster_eq_empty_of_pole_not_mem` (`CompactCenterCrossings.lean:18`),
   retains the same ρ for all t and z, and reorders those two universal
   quantifiers. For a pole inside the enclosing disc, the sharp counting and
   punctured comparison above address the pole-containing case. These steps
   address the proof gaps G32(a)-(d) recorded in `GRAPH.md:1521-1545` at the
   level of the checked Lean chain; they are not a complete semantic audit of
   its many analytic and topological helper definitions.

## Circularity and validation

A Lean environment traversal followed `ConstantInfo.value? (allowOpaque :=
true)` and `Expr.getUsedConstantsAsSet` recursively for `HarmonicBalls.` names
only. It reached 1,871 project values for the two-input provider and 1,990
for the three-input provider. Examining the types of all reached declarations,
the only direct references to `ClusterBoundedCrossingsStmt` were the two
roots and the forward intermediate producers at `DyadicCrossingAssembly.lean:
108-125`; there were no direct references to
`CrossingComponentContainsClusterCrossingStmt` (10.5). I2 producers occur in
the three-input closure as expected; none occur in the two-input closure.
The observed 10.1 producers are arranged in the forward applications described
above, not fed back into themselves. This is a bounded value/name test: it
skips non-project constants, references hidden by non-project wrappers, and
arbitrary semantically equivalent renamed propositions. The inspected local
analytic comparison is discharged as above, but no complete semantic
non-equivalence theorem for every transitive helper is claimed.

The traversal can be reproduced with `lake env lean` on a temporary file
containing the following command (the output counts both root and generated
project constants):

```lean
import HarmonicBalls.Proofs.Sec10.PrevalenceCrossingAssembly
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for root in #[`HarmonicBalls.clusterBoundedCrossings_of_volumeGrowth_and_zero_existence,
      `HarmonicBalls.clusterBoundedCrossings_of_three_staged_inputs] do
    let mut seen : Std.HashSet Name := {}
    let mut todo : Array Name := #[root]
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if !seen.contains n && n.toString.startsWith "HarmonicBalls." then
        seen := seen.insert n
        if let some ci := env.find? n then
          if let some v := ci.value? (allowOpaque := true) then
            for dep in v.getUsedConstantsAsSet.toArray do
              if !seen.contains dep && dep.toString.startsWith "HarmonicBalls." then
                todo := todo.push dep
    logInfo m!"ROOT {root}: {seen.size} project values"
    for n in seen.toArray.qsort Name.quickLt do
      if let some ci := env.find? n then
        let ty := ci.type.getUsedConstantsAsSet
        if ty.contains `HarmonicBalls.ClusterBoundedCrossingsStmt ||
            ty.contains `HarmonicBalls.CrossingComponentContainsClusterCrossingStmt then
          logInfo m!"TARGET IN TYPE {n}"
```

`~/paper-fleets/hb/lc archive/HarmonicBalls/Audit/Section10CrossingExports.lean` and
`~/paper-fleets/hb/lb HarmonicBalls.Audit.Section10CrossingExports` pass.
Each provider's `#print axioms` is exactly `[propext, Classical.choice,
Quot.sound]`. The audit module has no placeholders. These facts certify the
conditional Lean terms, not literature validity, source equivalence, full
semantic closure, or numbered-result closure.
