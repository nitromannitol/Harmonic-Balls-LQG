# Countable circle-profile decoder audit

Scope: the deterministic Borel decoder of r10 `l:r6-transfer`
(`~/paper-fleets/hb/notes/sec11-proof/sec11-proof-r10.tex`, lines 927-950: "There is a Borel decoder
from `R^{J_Q}` to `A` ..."). This packet is only that decoder. It does not close field reconstruction, the Palm
identity, measure or metric transfer, `RawToProfileStep`, or any numbered result.

Lean file: `HarmonicBalls/Proofs/Sec11/ClosureScales/CountableCircleDecoder.lean` (module
`HarmonicBalls.Proofs.Sec11.ClosureScales.CountableCircleDecoder`).

## Statement

- `J = CircleDomain := {p : ℝ × ℂ // 0 < p.1}` with its subtype topology (line 31).
- `C(J, ℝ)` with the compact-open topology, and its Borel sigma-algebra (Mathlib's
  `ContinuousMap.measurableSpace`, which is `borel`).
- `circleBox m = {p : J | 1/m ≤ p.1.1 ∧ p.1.1 ≤ m ∧ ‖p.1.2‖ ≤ m}` (line 34), the box `K_m`; `m : ℕ`
  with `2 ≤ m` is the same as an integer `m ≥ 2`.
- `exists_measurable_circle_decoder` (line 71): for countable `I`, `q : I → J` with `DenseRange q`,
  `_h_one : ∃ i, (q i).1 = (1, 0)` and `_h_box : ∀ m ≥ 2, circleBox m ⊆ closure (range q ∩ circleBox m)`,
  there is `decode : (I → ℝ) → C(J, ℝ)` with `Measurable decode` (product sigma-algebra on `I → ℝ`),
  `decode (fun i => f (q i)) = f` for every `f`, and `decode a = 0` whenever no continuous `f` has
  `f (q i) = a i` for all `i`.
- Named decoder `circleDecoder q` (line 88), landed together with its characterizations:
  `circleDecoder_measurable` (line 92), `circleDecoder_restrict` (line 98, left inverse),
  `circleDecoder_valid_iff` (line 111, a code is valid iff the decoded function reproduces it on `range q`),
  and `circleDecoder_of_not_valid` (line 103, zero on invalid codes).

## Route

1. `C(J, ℝ)` is Polish (line 44). Second countability is Mathlib's
   `ContinuousMap.instSecondCountableTopology`, from local compactness (line 38) and second countability of `J`.
   Complete metrizability comes from `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable`
   on `ContinuousMap.compactConvergenceUniformSpace`. That uniformity is complete
   (`instCompleteSpaceOfCompactlyCoherentSpace`), countably generated (CompactConvergence.lean:233), and its
   topology is the compact-open topology by construction (`replaceTopology`).
2. The restriction map `Φ f = (f (q i))_i` is continuous (`continuous_circleRestrict`, line 49) and injective
   when `q` has dense range (`injective_circleRestrict`, line 55, by `Continuous.ext_on`).
3. Lusin–Souslin (`Continuous.measurableEmbedding`, Mathlib `MeasureTheory/Constructions/Polish/Basic.lean`)
   makes `Φ` a measurable embedding. `MeasurableEmbedding.measurable_extend` then makes
   `Function.extend Φ id (fun _ => 0)` measurable. `Function.Injective.extend_apply` and
   `Function.extend_apply'` give the two inverse properties.

## Deviations and observations

- The written construction of r10 is not formalized: countably many rational uniform-continuity conditions on
  the boxes, extension on each box, gluing, and limits of coded evaluations. The existence statement is
  proved by the route above, which needs no premise beyond Mathlib.
- The source sentence "This is a separable complete metrizable space" is now proved in Lean, not assumed.
  Separability is Mathlib's `ContinuousMap.instSeparableSpace`.
- `_h_one` and `_h_box` are not used by the proof; they are kept as the source states them, and are underscore-named
  to say so. Reading observation, not formalized: `_h_box` follows from `DenseRange q`. Each `K_m` is the closure in
  `J` of its interior `{1/m < p.1 < m, ‖p.2‖ < m}`, and every nonempty open subset of `J` meets `range q`.
- No literature input, no `Proposed` or `External` file, no edit to `Defs`, `Draft`, `FROZEN`, or the paper.
  No Lattice-Probability or Bonanno code is consumed, so no credit line is needed.

## Checks

- `lc` on the file: CHECK OK, no warnings.
- `lb HarmonicBalls.Proofs.Sec11.ClosureScales.CountableCircleDecoder`: BUILD OK.
- `#print axioms` (scratch file outside the repo): `exists_measurable_circle_decoder`, `circleDecoder_measurable`,
  `circleDecoder_restrict`, `circleDecoder_of_not_valid`, `circleDecoder_valid_iff`, `injective_circleRestrict`
  each depend only on `propext`, `Classical.choice`, `Quot.sound`.
- Token scan of the file: no `sorry`, `axiom`, `admit`, `native_decide`, or `maxHeartbeats`.
