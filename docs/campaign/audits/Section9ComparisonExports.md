# Section 9 comparison export audit

2026-11-05. **Conditional composition PASS; source/semantic seal NOT
ESTABLISHED.** The two exports are implications with undischarged premises;
none of 9.3, 9.4, or weak 9.2 is thereby an unconditional numbered closure.
The three Proposed inputs await operator source-check, and 8.2 is unproved.

## Pins and source reconstruction

`FROZEN.md:69-72` names the exact Prop definitions
`HarmonicBalls.SubharmonicBallUniquenessWeakStmt` (weak 9.2),
`HarmonicBalls.HarmonicBallBoundarySubsetStmt` (9.3), and
`HarmonicBalls.RegularOpenEqOfAEEqStmt` (9.4), respectively at
`Draft/Section9.lean:125-132,144-151,158-164`. The same file's SHA-256 is
`42365b5d9e05e204baf5a31279971e4e12205bd011b7980ba75a4d04a0960827`;
its last change is bd58fe68c095a691b20cc287f4a110453371bbc2. The frozen
list gives no declaration-byte hashes, source hash, provider mapping, versioned
anchor IDs, or proof-seal state; an exact manifest-bound seal cannot be verified.
These are `def : Prop`, not frozen theorem bodies.

Paper `paper/lqg_harmonic_ball-corrected.tex:2315-2327` prints strong 9.2;
its proof only derives raw-cluster inclusion. E33(a), `FROZEN.md:7-10,69-70`,
authorizes a *separate* weak statement: raw cluster included in A, but the
null-difference clause still uses its regularization. We do not assert the
printed strong statement. Paper 2331-2390 gives 9.3: simultaneously a.s.,
for each harmonic ball A compactly contained in a disc and with positive mass t,
its boundary is in the closure of the whole-plane regularized cluster of the
same centre and mass. Paper 2392-2409 gives 9.4: a.s., two open regular open
sets with mutually null differences are equal. Global standing setting is
paper 355-396 and cluster family Theorem 5.5 at 863-868.

E23 (`~/paper-fleets/hb/ESCALATIONS.md:117-120`) exhibits narrow-test-class
counterexamples. C22, adopted together with C7 by `FROZEN.md:10,71`, reads
9.3 using the enlarged class. C7 reads its auxiliary open O as bounded with
`closure A ⊆ O` (`Defs/HarmonicBall.lean:94-104`). C10 applies only to the
separate weak 9.2; E33(a) supersedes earlier provisional descriptions. The
corrected and original TeX currently have identical SHA-256
`8fdbb03043011800560e4d947eb79a3cfdd7cc8767a3af94469f04201b7593fc`;
`docs/campaign/CORRECTIONS.md:4` states none are inserted. E49 therefore
remains open: the frozen operator rulings and raw source must both be consulted,
and the supposedly corrected TeX does not independently certify C7/C22.

## Expanded frozen binder classification

Groups below preserve the outer-to-inner order. Counts classify groups rather
than individual variables; nested GFF and LQG fields are listed separately.
SOURCE and RULED are source/ruling readings, STANDING refers to source setup
or the explicitly referenced Theorem 5.5, TYPING to realization/carrier data,
and EXCESS to added analytic assumptions. This is a conditional surface audit,
not certification of all underlying constructions.

| Applies | Binder or expanded group | Bin | Evidence |
| --- | --- | --- | --- |
| all | γ, 0 < γ, γ < 2; α₀ < Q | STANDING | TeX 355-396 |
| all | Ω, measurable-space instance, P, field observables and μ | TYPING | realization of standing setting; ℂ carrier |
| all | GFF: measurable test pairings and positive-radius circle averages | STANDING | `Defs/GFF.lean:93-99` |
| all | GFF: joint Gaussianity, zero means, covariance kernel | STANDING | `Defs/GFF.lean:100-106`, TeX 355-380 |
| all | GFF: a.s. continuous positive-radius circle process | STANDING | `Defs/GFF.lean:107-109`; requires full source audit |
| all | LQG measure: a.s. local finiteness and dyadic vague limit of circle-average approximations | STANDING | `Defs/LQG.lean:45-75`; source 390-396, dyadic version requires full source audit |
| 9.3 | Λhat random family with a.s. for every z the 5.5 properties | STANDING | TeX 863-868, 2336-2344; choice of family explicit |
| 9.3 | family mass, null boundary, regular openness, boundedness, connectedness, centre | STANDING | `Draft/Section1.lean:58-70`, 5.5 |
| 9.3 | family monotonicity, Hausdorff continuity, intersection {z} | STANDING | `Draft/Section1.lean:71-76`, 5.5 |
| 9.3 | each positive-time family member is a subharmonic ball | STANDING | `Draft/Section5.lean:88-90`, 5.5 |
| 9.3 | family equals disc regularization for every sufficiently large disc containing its closure | STANDING | `Draft/Section5.lean:90-91`, TeX 863-868 |
| all | a.s. ω before all geometric variables | SOURCE | TeX 2317, 2337, 2394 |
| 9.3 | A,z,R,t; z ∈ B_R, closure A ⊆ B_R | SOURCE | TeX 2336-2337; compact containment in ℂ |
| 9.3 | A open, contains z, positive finite mass; narrow harmonic mean-value class | SOURCE | `Defs/HarmonicBall.lean:71-81`; source ball convention |
| 9.3 | additional enlarged test class: bounded open O containing closure A, harmonic plus signed Green potential supported off A, with integrability | RULED | C7/C22; `Defs/HarmonicBall.lean:87-104` |
| 9.3 | t > 0 and μ A = ofReal t | SOURCE | TeX 2337 |
| 9.4 | X,Y subsets ℂ, each open and equal to interior of closure | SOURCE | TeX 2394-2396 |
| 9.4 | μ(X\\Y)=0 and μ(Y\\X)=0 | SOURCE | TeX 2396 |
| weak 9.2 | A,z,t,R; t,R > 0, z ∈ B_R, closure A ⊆ B_R | SOURCE | TeX 2317 |
| weak 9.2 | A open, contains z, positive finite mass; submean inequality and integrability for all subharmonic tests | SOURCE | `Draft/Section4.lean:65-82`; TeX 742-750 |
| weak 9.2 | subharmonic tests q + Gν₁ − Gν₂, O open contains closure A, compactly supported finite νᵢ, ν₁ A=0, harmonic q; ν₂ has no atom at z and its potential there is integrable | SOURCE | `Draft/Section4.lean:65-71`; finite-at-centre/junk-value reading requires semantic audit |
| weak 9.2 | μ A = ofReal t | SOURCE | TeX 2317 |

Counts by group: 9.3 SOURCE 4, STANDING 10, TYPING 1, RULED 1,
EXCESS 0 (16); 9.4 SOURCE 3, STANDING 5, TYPING 1, RULED 0,
EXCESS 0 (9); weak 9.2 SOURCE 5, STANDING 5, TYPING 1, RULED 0,
EXCESS 0 (11). The weak conclusion itself is RULED by C10/E33(a).
These classifications do not establish source equivalence of all nested objects.
The family a.s. hypothesis is a separately supplied 5.5 object, not an extra
regularity hypothesis on arbitrary A. Its representation and all nine family
fields remain explicit in the definition; the provider consumes only
boundedness, mass, and the positive-time subharmonic-ball field.

## Conditional assumptions and actual use

`Audit/Section9ComparisonExports.lean` checks each provider with its full
outer input types expanded. For the first export the inputs are:

* `WholePlaneLQGBallMassBounds`, including the polynomial tail and both
  exponent inequalities: Ding–Gwynne 2020, Lemma 3.8 p.25;
  `Proposed/LQG.lean:146-151`.
* `LQGMeasureCoordChange` at zero strength, simultaneously for all nonzero
  complex affine maps: Duplantier–Sheffield 2011 Prop. 2.1 p.13 and
  Sheffield–Wang 2016 Thms. 1.1 and 1.4; `Proposed/LQG.lean:108-112`.
* `LQGMeasureExistence` at every α < Q, on the specified probability space:
  Duplantier–Sheffield 2011 Prop. 1.1 p.5 and Berestycki–Powell Thm. 2.1
  p.62; `Proposed/LQG.lean:64-66`.

All three are staged pending source-check, including the exact simultaneous
and on-space scopes; the listed source citations are the Proposed docstrings,
not independent source approval. They are EXCESS relative to the unconditional
frozen results, never hidden as standing hypotheses. I2 is derived by
`ExistenceResultsAssembly.lean:36-49` from the three, using proved affine
invariance and Weyl scaling, zero-strength existence, and non-atomicity from
existence at stronger subcritical singularity. The two outputs explicitly
consume the derived I2 at lines 51-55.

For weak 9.2, `AffineInvarianceAssembly.lean:27-31` takes the exact I2 and
`TypicalPointManyGoodScalesStmt` 8.2 as independent explicit hypotheses. The
Lean example expands both, including the a.s.-then-μ-typical-point quantifier,
the eventual natural scales, and constant order. I2 is the all-scales,
all-centres two-sided ball bound in `Draft/Section2.lean:122-130`; 8.2 is
`Draft/Section8.lean:74-85` and is unproved. No rooted-law premise occurs in
the provider type; any rooted-law work required to establish 8.2 is upstream
and is not discharged by this export. The 8.2 binder-strength/source question
G28 remains subject to its own frozen reading and source review.

For 9.4, `VolumeGrowthAssembly.lean:11-13` derives I1 full support from I2
(`Steps/Sec2/VolumeGrowth.lean:220`), then
`RegularOpenEqOfAEEq.lean:19-35` proves each inclusion from positivity on
nonempty open sets; no regularity of μ beyond open positivity is assumed.
For 9.3, `HarmonicBoundaryAssembly.lean:20-46` obtains local finiteness and
volume growth from I2, derives full support, intersects both events with the
family event, enlarges the disc using boundedness, and uses the family's mass
and subharmonic-ball fields. `StrongMinimum.lean:57-90` applies the actual
continuous auxiliary Green potential, its Laplacian, superharmonic minimum
principle and full support. The analytic regularity is derived from volume
growth rather than supplied as a hidden top-level premise. The harmonic test
class explicitly includes Green functions with poles outside A, including
boundary points (`Defs/HarmonicBall.lean:139-177`); this is precisely the
C7/C22-sensitive path, not the narrower harmonic-near-closure class.

For weak 9.2, `DyadicGlobalUniqueness.lean:19-44` derives 6.11 from I2,
combines it with cluster openness and 8.2 to obtain unit-disc boundary nullity
(`Proofs/Sec8/ClusterBoundary.lean:89-115`), and uses the proven GFF affine
invariance `AffineInvarianceAssembly.lean:16-22`. Dyadic scaling
(`LQGSpatialDilation.lean:184-194`) and compatibility on a cofinal radius
sequence (`CofinalBoundaryRadii.lean:27-70`) transfer nullity to all radii.
`WeakUniqueness.lean:29-44` derives raw cluster inclusion, compact containment,
then mass equality from conservation and boundary nullity; finally
`SubharmonicSupersolution.lean:54-78` proves the stated inclusion and null
difference. No arbitrary-A regular openness or rooted law is assumed.

## Dependency and circularity checks

The following bounded traversal recursively visits *project-named constants
in values*, including opaque theorem values, and checks direct type references.
It found 457 project constants for the 9.3/9.4 root and 963 for the weak-9.2
root. The first has I2 producers and the forward 9.3/9.4 producers; it has no
direct weak or strong 9.2 type reference. The second has no I2 producer and
no direct 9.3, 9.4, or strong 9.2 type reference; its weak-9.2 references are
the forward providers `...of_boundaryNull`, `...of_cofinalRadii`,
`...of_dyadicRadii`, `...of_dyadic_affine`, `...of_dyadic_typical_scales`,
`...of_dyadic_volumeGrowth`, and the root. Inspection of their bodies confirms
the forward chain described above. No top-level premise is syntactically a
target or an obvious restatement of it. This is not a proof against arbitrary
semantic equivalence, non-project wrappers, or circular assumptions concealed
in every analytic definition; those remain a semantic-seal limitation.
Reproduce with `lake env lean` on the following temporary file:

```lean
import HarmonicBalls.Proofs.Sec9.ExistenceResultsAssembly
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for root in #[`HarmonicBalls.section9_comparison_lemmas_of_existence,
      `HarmonicBalls.subharmonicBallUniquenessWeak_of_volumeGrowth_typicalScales] do
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
    logInfo m!"ROOT {root}: {seen.size} project constants"
    for n in seen.toArray.qsort Name.quickLt do
      if let some ci := env.find? n then
        let ty := ci.type.getUsedConstantsAsSet
        if ty.contains `HarmonicBalls.HarmonicBallBoundarySubsetStmt ||
           ty.contains `HarmonicBalls.RegularOpenEqOfAEEqStmt ||
           ty.contains `HarmonicBalls.SubharmonicBallUniquenessWeakStmt ||
           ty.contains `HarmonicBalls.SubharmonicBallUniquenessStmt ||
           ty.contains `HarmonicBalls.LQGVolumeGrowthAllScalesStmt then
          logInfo m!"MATCH {n}"
```

The compiled examples check the three expanded frozen target types and exact
conditional applications. `#print axioms` for both exports gives only
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` or custom axiom appears.
The standing GFF/LQG structures, obstacle construction, singular Green-potential
conventions, and all transitive analytic helper meanings have not been fully
source-audited here. Compilation, this bounded dependency test, and the binder
classifications therefore do not provide a full semantic seal.
