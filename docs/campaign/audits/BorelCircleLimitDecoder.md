# Audit: BorelCircleLimitDecoder (task sec11-borel-circle-limit-decoder)

Module: `HarmonicBalls/Proofs/Sec11/ClosureScales/BorelCircleLimitDecoder.lean` (new).
Source: r10 `l:r9-circle-code`, `notes/sec11-proof/sec11-proof-r10.tex` lines 1313-1323 (the Borel map `C`), with the
decoder of lines 927-950.
Imports: `CountableCircleDecoder` (commit 4202e55) and `PalmPairingMeasurable` (for `pairingMeasSpace`). No new
hypothesis and no External or Proposed input. The import of `PalmPairingMeasurable` brings
`Proposed/DuplantierMillerSheffield` into the import closure; no declaration of that module is used here.

## Statements (namespace `HarmonicBalls`)

- `exists_measurable_circle_limit_decoder {S I} [MeasurableSpace S] [Countable I] (q : I → CircleDomain)
  (hq : DenseRange q) (a : I → ℕ → S → ℝ) (ha : ∀ i n, Measurable (a i n))`: there is `C : S → C(CircleDomain, ℝ)`
  with `Measurable C` and
  (i) `∀ s F, (∀ i, Tendsto (fun n => a i n s) atTop (𝓝 (F (q i)))) → C s = F`, for continuous `F`;
  (ii) `∀ s, (¬ ∃ F, ∀ i, Tendsto (fun n => a i n s) atTop (𝓝 (F (q i)))) → C s = 0`.
- `exists_measurable_circle_limit_decoder_pairing {I} [Countable I] (q) (hq) (psi : I → ℕ → ℂ → ℝ)
  (hpsi : ∀ i n, IsTestFunction Set.univ (psi i n))`: the same, with `S = (ℂ → ℝ) → ℝ`, measurability for
  `pairingMeasSpace`, and `a i n T = T (psi i n)`.
- `circleLimitDecoder_unique`: any `D` with (i) and (ii) equals `circleLimitDecoder q a`. Density of `q` makes the
  continuous `F` in (i) unique, so (i) and (ii) determine the map completely.

Definitions: `seqLimitOrZero u` (`limUnder atTop u` where `u` converges, `0` otherwise);
`circleLimitDecoder q a s` (if every `n ↦ a i n s` converges, `circleDecoder q (fun i => seqLimitOrZero (fun n =>
a i n s))`; otherwise `0`).

## Proof route

- Measurability: the convergence locus of each coordinate is measurable (`measurableSet_exists_tendsto`).
  `StronglyMeasurable.limUnder` (Mathlib, `Polish/StronglyMeasurable.lean`) gives the measurability of `limUnder`.
  `measurable_seqLimitOrZero` is the indicator of the locus of that limit. Coordinates: `measurable_pi_iff`. The
  all-coordinates locus is a countable intersection (`MeasurableSet.iInter`). The decoder is `circleDecoder_measurable`
  composed with the coordinate map, glued to `0` by `Measurable.ite`.
- (i): `seqLimitOrZero_eq_of_tendsto` (uniqueness of limits in `ℝ`) turns each coordinate into `F (q i)`;
  `circleDecoder_restrict` (from `injective_circleRestrict`) returns `F`.
- (ii): if every coordinate converges, the limit vector `L` is invalid: a valid `F` with `F (q i) = L i` would make
  every sequence converge to `F (q i)`, contrary to the hypothesis. `circleDecoder_of_not_valid` gives `0`. Otherwise
  the output is `0` by definition.
- Pairing: `measurable_pairing_eval` (`measurable_iff_comap_le`, `le_iSup_of_le`, after unfolding `pairingMeasSpace`
  and `pairingSigmaAlgebra`) gives measurability of `T ↦ T (psi i n)`. The general theorem then applies.

## Reading of r10

- "take the limits of these test evaluations where they exist": a code with any coordinate lacking a limit is
  invalid, and the output is `0`. This follows the task convention; the r10 wording is read this way.
- "decode ... by the continuous-function decoder": `circleDecoder` (`CountableCircleDecoder.lean`, `Function.extend`
  of the restriction map), which returns `0` on invalid codes.
- Not formalized (later consumers, per the task): the identification of `C` with the circle profile on the conull
  event, the Gaussian L2 estimates, the deterministic sequences, the H^-2 reconstruction, the compatible shifts, and
  the `RawToProfileStep` consumers (E56 ruling pending). No `CanonicalProfile` declaration is touched.

## Checks

- `lc` (with `-DwarningAsError=true`): CHECK OK.
- `lb HarmonicBalls.Proofs.Sec11.ClosureScales.BorelCircleLimitDecoder`: BUILD OK.
- `#print axioms`, from a scratch file under `/tmp` outside the repository, for `exists_measurable_circle_limit_decoder`,
  `exists_measurable_circle_limit_decoder_pairing`, `circleLimitDecoder_unique`,
  `circleLimitDecoder_of_not_exists`, `measurable_pairing_eval`: each depends on `propext`, `Classical.choice`,
  `Quot.sound` only.
- Raw grep (comments included) for `sorry`, `axiom`, `admit`, `native_decide`, `maxHeartbeats`: no match.

## Provenance and credit

- Mathlib APIs used: `measurableSet_exists_tendsto`, `StronglyMeasurable.limUnder`, `Measurable.indicator`,
  `Measurable.ite`, `measurable_pi_iff`, `measurable_iff_comap_le`. `Measurable.limsup` (`BorelSpace/Order.lean`) gives
  the limsup, not the limit with zero off convergence, so it is not used.
- Lattice-Probability (Bonanno): the module imports no Lattice-Probability declaration. `pairingSigmaAlgebra`
  (`HarmonicBalls/Defs/LQGMetric.lean:133`) and `IsTestFunction` (`HarmonicBalls/Defs/Laplacian.lean:47`) are project
  definitions. No credit line is added. Operator to confirm whether these definitions are adapted from his code.
- No new literature premise, numbered closure, metric moment or Pfeffer membership.
