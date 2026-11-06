# Section 5 strong compatibility: exhaustion audit

Target: `HarmonicBalls.ClusterStrongCompatibilityStmt`, Lemma 5.8, frozen in `docs/campaign/FROZEN.md:49` under C21. The campaign freezes proposition aliases rather than the versioned one-declaration manifest in the generic audit workflow. Draft/Section5.lean SHA-256 `0e990dd0a0bc11dee3cda666581a4de6e2d1556face434ee87fe7853a2a37e62` agrees with its frozen bytes at bd58fe6; corrected TeX SHA-256 `8fdbb03043011800560e4d947eb79a3cfdd7cc8767a3af94469f04201b7593fc` (no frozen source hash recorded). Source: corrected TeX 1014–1025, 583–592, 863–868, 132–160, 355–398; C21 restricts the pole to U. The printed lemma says z in C; this audit uses the adopted ruling and does not assert the unrestricted printed version.

## Binder and scope audit

Each row is a binder or a logical component of a bundled binder. Counts treat grouped parameters and each field as one row; implication conclusions are not inputs.

| Binder or expanded component | Bin | Source or role |
|---|---|---|
| γ and 0 < γ, γ < 2 | STANDING | TeX 132–135 |
| α₀ and α₀ < Q | STANDING | TeX 373; no α₀ = 0 restriction |
| Ω, measurable-space instance, P, hC, hcirc, μ | TYPING | probability realization, TeX 355–398 |
| GFF measurable pairings | STANDING | Defs/GFF.lean:93; field at 355–365 |
| GFF measurable circle averages | STANDING | same |
| joint Gaussian process | STANDING | same |
| centered observable law | STANDING | same |
| covariance law | STANDING | same |
| almost-sure circle continuity | STANDING | same; chosen modification |
| LQG locally finite limit | STANDING | Defs/LQG.lean:53,73; TeX 390–398 |
| LQG dyadic vague convergence | STANDING | same; full-source equivalence remains unverified |
| Λhat and its all-centres almost-sure family assumption | SOURCE | 1019–1022 and Theorem 5.5; family expanded below |
| deterministic U, openness and boundedness | SOURCE | 1019–1021, fixed before final event |
| z ∈ U | RULED | C21 |

Counts: SOURCE 2, STANDING 10, TYPING 1, RULED 1, EXCESS 0. Within the event, t > 0 and z ∈ U are universal, followed by the disjunction `closure Λhat ⊆ U ∨ closure clusterOn ⊆ U` and closure equality. The two alternatives are independently sufficient. Compact containment here agrees with closure inclusion because U is bounded. The representative family is universally quantified before U; the event is after U and covers all t and z simultaneously.

`IsRegularizedClusterFamily` (Draft/Section5.lean:88) comprises the nine conditions of Draft/Section1.lean:58: positive-time mass and null frontier, regular openness, boundedness, connectedness, centre membership, monotonicity, Hausdorff continuity, and intersection equal to the centre; it also includes all positive-time subharmonic-ball properties and the exact all-larger-disc regularized-cluster representation whenever the family closure lies in a positive disc. The family assumption is retained in full, not replaced by an existence claim. Its subharmonic test class has not been independently certified here.

## Conditional assembly and actual use

`Audit/Section5ExhaustionCompatibility.lean` proves `clusterStrongCompatibility_of_regular_exhaustions : LQGVolumeGrowthAllScalesStmt → (explicit regular-exhaustion property) → ClusterStrongCompatibilityStmt`. The return type is the actual frozen alias, checked by elaborating its exact application, not a nearby reformulation. The exhaustion property has, for every bounded open U and z ∈ U, open monotone Vₙ whose union is U, closures contained in U, z in each Vₙ, and Green boundary limits zero at every point of closure Vₙ outside Vₙ. It is a proof premise, EXCESS relative to Lemma 5.8; I2 is likewise a derived proof premise, not a new source assumption or literature input. I2 has staged conditional producers, not an unconditional certification here.

`ae_isLocallyFiniteMeasure_volumeGrowth` (Steps/Sec3/Basic.lean:71) consumes I2 and the standing field/measure assumptions to obtain deterministic exponents and one event with local finiteness and growth at every positive radius. Intersecting this with the given family event precedes the universal t and z. For each z, the proof selects the exhaustion and invokes `regularizedFamily_closure_eq_clusterOn_of_regular_exhaustion` (Proofs/Sec5/ExhaustionClusterCompatibility.lean:756) with the original disjunction. The comparison treats the two disjuncts separately, uses monotonicity and eventual stabilization, and passes to the union. It assumes neither Green regularity nor admissibility of the infimum on ambient U; regularity is demanded only on the exhaustion stages. No additional Lemma 3.2 input occurs in this export.

The separate `exists_greenRegular_exhaustion` (Proofs/Potential/GreenRegularDomainExhaustion.lean:129) is a proved restricted exterior-disc construction; it is deliberately not imported or applied by this conditional audit. The older universal finite-disc boundary premise is false: `four_disc_union_irregular_boundary` (GreenRegularBoundaryGeometry.lean:706) proves a four-disc union with an irregular boundary point. E52 is not discharged by that premise. A subsequent exact source/semantic audit and explicit application of the restricted producer are needed before any numbered closure claim.

## Definition and semantic checks

`supersolutionsOn` (Draft/Section5.lean:103) requires continuity on closure U, distributional Laplacian bound, and obstacle dominance off the pole; `leastSupersolutionOn` (:109) is real `sInf` of evaluation values. Real `sInf` returns zero for an empty or unbounded-below set, including potentially at the pole. `clusterOn` (:114) explicitly inserts the pole and uses the strict obstacle inequality elsewhere; it does not assert finiteness of that infimum at the pole. The exhaustion comparison uses off-pole infimum estimates (e.g. ExhaustionClusterCompatibility.lean:358–391) and set membership with explicit pole, not an assumed ambient admissible infimum. This is an exact Lean consumption observation, not a proof that the real-valued construction always realizes the paper's extended infimum.

`greenFunction` (Defs/Green.lean:70) uses the normalized logarithmic kernel and greatest harmonic minorant, with zero on the diagonal and outside the domain; irregular boundary behavior is not assumed to match zero. The paper's claimed verbatim general-domain extension and full characterization of the source obstacle object remain unaudited at irregular boundaries (G9/E46). LQG uses dyadic vague convergence and the Gaussian field is encoded by observables and circle averages; complete equivalence to all source objects, and the family test-class semantics, remain unverified. Thus semantic verdict is FAIL CLOSED: BODY_MATCH, PUBLIC_CARRIER and CHARACTERIZATION are not certified; WELL_DEFINEDNESS is N/A for literal predicates and CHOICE_INDEPENDENCE is not established as a global characterization. This does not challenge the conditional Lean equality.

Validation: lock-free compile and shared build of the audit module; `#print axioms clusterStrongCompatibility_of_regular_exhaustions` reports only `propext`, `Classical.choice`, `Quot.sound`. No placeholders or additional axioms are introduced. The imported potential-theoretic infrastructure uses Leonardo Bonanno's code. Conditional composition passes; Lemma 5.8 is not counted as closed.
