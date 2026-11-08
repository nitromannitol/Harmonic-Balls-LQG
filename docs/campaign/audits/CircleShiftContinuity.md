# CircleShiftContinuity: joint continuity of the circle-code insertion on the actual carrier

Lean module: `HarmonicBalls/Proofs/Sec11/ClosureScales/CircleShiftContinuity.lean` (namespace `HarmonicBalls`).
Status: DONE for this packet. `lc` OK, `lb` BUILD OK, no forbidden tokens, printed axioms as recorded below.

## Source and claim

- Written proof `notes/sec11-proof/sec11-proof-r10.tex` (fleet path, outside the repository), lemma
  `l:r9-circle-code`: the literal insertion (equation `eq:r9-Gamma`) is at TeX lines 1257-1284; the proof paragraph
  "Finally, `Γ` is jointly Borel, in fact continuous `𝒜×ℂ→𝒜`" is at TeX lines 1380-1392.
- Independent audit: `notes/sec11-proof/AUDIT-r9.md` line 18, table row `1027–1038` ("Joint measurability of insertion
  maps"). These numbers are round-9 TeX lines, not Markdown lines; the round-10 counterpart is TeX 1380-1392. The row
  `999–1025` (AUDIT-r9.md line 17) is the reconstruction row (round-10 TeX 1353-1378) and is not the claim treated here.
  `notes/sec11-proof/AUDIT-r10.md` line 110 retains the round-9 circle decoder proof.
- Claim formalized: on the carrier `C(CircleDomain, ℝ)` (`CircleDomain = {p : ℝ × ℂ // 0 < p.1}` with its subspace
  topology; compact-open topology on the function space), `(γ, z, F) ↦ circleDMSShiftFun γ z F` is continuous, hence
  jointly Borel; and `u ↦ circleAverageFun u u.continuous` is continuous on `C(ℂ, ℝ)`. The source's `𝒜` is identified
  with the repository carrier `C(CircleDomain, ℝ)`. No other carrier, profile convention, validity predicate, bound at
  infinity, or continuous-insertion premise is introduced. Both conclusions are deterministic: no probability space,
  reconstruction, `H^{-2}` space, or raw pairing enters.

## Public theorem types (exact Lean statements)

Namespace `HarmonicBalls`; all have only the displayed hypotheses.

1. `continuous_circleAverageFun : Continuous (fun u : C(ℂ, ℝ) => circleAverageFun u u.continuous)`
2. `continuous_circleDMSShiftFun : Continuous (fun p : ℝ × ℂ × C(CircleDomain, ℝ) => circleDMSShiftFun p.1 p.2.1 p.2.2)`
3. `measurable_circleDMSShiftFun : Measurable (fun p : ℝ × ℂ × C(CircleDomain, ℝ) => circleDMSShiftFun p.1 p.2.1 p.2.2)`
4. `measurable_circleDMSShiftFun_comp {S : Type*} [MeasurableSpace S] {γ : S → ℝ} {z : S → ℂ} {F : S → C(CircleDomain, ℝ)} (hγ : Measurable γ) (hz : Measurable z) (hF : Measurable F) : Measurable fun s => circleDMSShiftFun (γ s) (z s) (F s)`
5. `continuous_circleDMSShiftFun_fixedGamma (γ : ℝ) : Continuous (fun q : C(CircleDomain, ℝ) × ℂ => circleDMSShiftFun γ q.2 q.1)`
6. `measurable_circleDMSShiftFun_fixedGamma (γ : ℝ) : Measurable (fun q : C(CircleDomain, ℝ) × ℂ => circleDMSShiftFun γ q.2 q.1)`
7. `measurable_circleAverageFun : Measurable (fun u : C(ℂ, ℝ) => circleAverageFun u u.continuous)`
8. `measurable_circleAverageFun_comp {S : Type*} [MeasurableSpace S] {U : S → C(ℂ, ℝ)} (hU : Measurable U) : Measurable fun s => circleAverageFun (U s) (U s).continuous`

Auxiliary public lemmas (the joint parametric statements the above depend on):

- `continuous_circleAverage_joint : Continuous fun q : C(ℂ, ℝ) × CircleDomain => Real.circleAverage q.1 q.2.val.2 q.2.val.1`
- `continuous_circleDMSShift_joint : Continuous fun q : (ℝ × ℂ × C(CircleDomain, ℝ)) × CircleDomain => q.1.2.2 q.2 - q.1.1 * Real.log (max q.2.val.1 ‖q.2.val.2 - q.1.2.1‖) + q.1.1 * Real.circleAverage logMaxOne q.2.val.2 q.2.val.1`

Specializations. Item 5 is the fixed-coefficient source assertion (`Γ_z` continuous in `(c, z)` with `γ` fixed). Items 4
and 8 are measurable composition with arbitrary measurable coefficient, root, profile, or family maps on any measurable
space `S`. Applying them to a decoder `D : Ω → C(CircleDomain, ℝ)` requires the caller to supply `Measurable D`; this
packet does not construct such a `D`.

## Proof route

1. `continuous_circleAverage_joint`: unfold `Real.circleAverage`; the integrand `(u, p, θ) ↦ u (circleMap p.2 p.1 θ)` is
   jointly continuous by continuity of evaluation (`continuous_eval`, `ℂ` locally compact); then
   `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` over `[0, 2π]`.
2. `continuous_circleAverageFun`: `ContinuousMap.continuous_of_continuous_uncurry` applied to step 1 (the uncurried
   direction needs no local compactness; Mathlib `Topology/CompactOpen.lean`).
3. `continuous_circleDMSShift_joint`: `F p` is jointly continuous by `continuous_eval` (`CircleDomain` is locally compact,
   `CountableCircleDecoder.lean:38`); `log max(r, |c - z|)` is continuous because `max(r, |c - z|) ≥ r > 0` on
   `CircleDomain` (`lt_max_of_lt_left`, `Continuous.log`); the circle average of `logMaxOne` is jointly continuous in
   `(c, r)` by `continuous_circleAverage_logMaxOne` (`RootedShiftProfile.lean:31`).
4. `continuous_circleDMSShiftFun`: `ContinuousMap.continuous_of_continuous_uncurry` applied to step 3.
5. Measurability: `Continuous.measurable` with the Borel σ-algebra on `C(X, Y)` (Mathlib
   `MeasureTheory/Constructions/BorelSpace/ContinuousMap.lean`: global instances `ContinuousMap.measurableSpace` and
   `BorelSpace`), and `Measurable.prodMk`/`Measurable.comp`. `C(CircleDomain, ℝ)` is second countable through the
   existing `PolishSpace` instance (`CountableCircleDecoder.lean:41-45`), so the product σ-algebra is Borel.
6. Item 5: `continuous_circleDMSShiftFun` composed with `(F, z) ↦ (γ, z, F)`.

No hypothesis on uniform bounds at infinity is used. The source's phrase "uniformly continuous on each compact parameter
set with `r` bounded below" is subsumed: continuity into the compact-open topology is proved on the whole carrier.

## Reuse

- Existing literal functions, unchanged: `circleDMSShiftFun`, `circleAverageFun`, and their `_apply` lemmas
  (`CircleDecoderAdditionCompatibility.lean:75-101`); `logMaxOne` and `continuous_circleAverage_logMaxOne`
  (`RootedShiftProfile.lean:23, 31`); `CircleDomain` with its `LocallyCompactSpace` and `PolishSpace C(CircleDomain, ℝ)`
  instances (`CountableCircleDecoder.lean:31, 38, 41-45`).
- Fixed-data continuity `continuous_circleDMSShift` and fixed-`u` continuity `continuous_circleAverage_domain`
  (`CircleDecoderAdditionCompatibility.lean`) are not sufficient: the joint versions above are new.
- Mathlib: `ContinuousMap.continuous_of_continuous_uncurry`, `continuous_eval`, `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`, `ContinuousMap.measurableSpace`, `BorelSpace C(X, Y)`.

## Checks

- `lc HarmonicBalls/Proofs/Sec11/ClosureScales/CircleShiftContinuity.lean`: CHECK OK (`logs/lc/215555-3325823.log`).
- `lb HarmonicBalls.Proofs.Sec11.ClosureScales.CircleShiftContinuity`: BUILD OK (`logs/lb/215614-3326266.log`).
- Forbidden tokens (`sorry`, `admit`, `axiom`, `native_decide`, `maxHeartbeats`) in the module: 0 raw hits, so 0 comment-aware hits.
- Printed axioms, from a check file outside the repository (`/tmp/z3check/CircleShiftAxioms.lean`, compiled by `lc`, log
  `logs/lc/215711-3329272.log`). Each printed declaration depends only on `[propext, Classical.choice, Quot.sound]`:
  `continuous_circleAverage_joint`, `continuous_circleAverageFun`, `continuous_circleDMSShift_joint`,
  `continuous_circleDMSShiftFun`, `measurable_circleDMSShiftFun`, `measurable_circleDMSShiftFun_comp`,
  `continuous_circleDMSShiftFun_fixedGamma`, `measurable_circleDMSShiftFun_fixedGamma`, `measurable_circleAverageFun`,
  `measurable_circleAverageFun_comp`.
- Credit (Bonanno). The non-Mathlib import closure of the module, from a transitive `^import` walk started at
  `CircleDecoderAdditionCompatibility`, is 20 modules (19 from that file's closure, plus the module itself). Zero of them
  are `LatticeProb`, `MarkovProcess` or `EllipticRegularity` modules. The Lattice-Probability port is not in the closure,
  so no credit line is required in the Lean file. (The 949-module closure recorded in `Sec11CirclePalmImportChecks.md`
  belongs to a different file that reaches `Proofs/Sec8/CircleLogPotential.lean`; it does not apply here.)

## Citation repairs (owned old audit notes; no Lean declaration changed)

- `CircleTestFubiniLimit.md`: the `dmsShift` item and the inputs paragraph now cite
  `HarmonicBalls.CirclePotential.circleAverage_log_norm_sub_eq_log_max` at `CirclePotential.lean:24` (the file had `:19`).
  The collision paragraph is replaced by the resolution recorded below.
- `MollifiedLogCircleLimit.md` line 48: qualified name; it is used in the proof of `circleAverage_log_sub`
  (`MollifiedLogCircleLimit.lean:151-157`).
- `MollifiedCircleGaussianL2.md` line 51: the identity is a project declaration. It was wrongly called a "Mathlib mean
  value identity"; Mathlib declares neither `circleAverage_log_norm_sub_eq_log_max` nor `circleAverage_log_sub`.

## Collision resolution

The unqualified name `circleAverage_log_norm_sub_eq_log_max` was carried by two declarations:
`HarmonicBalls.circleAverage_log_norm_sub_eq_log_max` (Section 8, `Proofs/Sec8/CircleLogPotential.lean:17`, unchanged)
and `HarmonicBalls.CirclePotential.circleAverage_log_norm_sub_eq_log_max` (Section 11,
`Proofs/Sec11/ClosureScales/CirclePotential.lean:24`, in namespace `HarmonicBalls.CirclePotential` since commit `2e35bf4`).
Every citation now uses the qualified name, so the clash is resolved.

## Open items (not closed by this packet)

- The source's continuity of `z ↦ k_z` into `H^{-2}_loc` (second paragraph of the proof, TeX 1380-1392) is not
  formalized. No `H^{-2}` space is introduced here.
- The distribution-valued consequences and the code identities of `eq:r9-code-identities` are outside this packet.
- The source assertion is formalized for the repository carrier `C(CircleDomain, ℝ)`. A different topology on the
  source's `𝒜`, if the paper intends one, would need its own argument; none is assumed here.
