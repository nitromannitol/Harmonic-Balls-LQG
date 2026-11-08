# Audit: CircleDecoderAdditionCompatibility (task sec11-circle-decoder-addition-compatibility)

Module: `HarmonicBalls/Proofs/Sec11/ClosureScales/CircleDecoderAdditionCompatibility.lean` (new, 239 lines).
Source: r10 written proof, `notes/sec11-proof/sec11-proof-r10.tex` lines 1313-1350 (Borel circle-limit decoder `C`, the
approximate-identity limit for a continuous addition, and the logarithmic insertion limit). Audited in `AUDIT-r9.md`
959-998 and reaffirmed in `AUDIT-r10.md` 110.

Imports: `BorelCircleLimitDecoder` (decoder, characterizations, uniqueness), `MollifiedCircleGaussianL2`
(`IsLiteralMollifier`, `circleMollifier`, `isTestFunction_circleMollifier`, `circleMollifier_eq`),
`MollifiedContinuousCircleLimit` (`mollified_continuous_circle_limit`), `MollifiedLogCircleLimit`
(`mollified_log_circle_limit`), `RootedShiftProfile` (`logMaxOne`, `continuous_circleAverage_logMaxOne`),
`Proposed.DuplantierMillerSheffield` (`dmsShift`, used as a definition only), and Mathlib.

Import closure: 19 modules including the file itself, no non-Mathlib package. The transitive walk finds no
`LatticeProb` (Lattice-Probability port) and no `Steps` module, so no credit line to Leonardo Bonanno is required.

## Declarations

- `circleCompatPsi` (:49): `psi i n = circleMollifier rho (q i).val.2 (q i).val.1 (eps i n)`.
- `circleCompatDecoder` (:54): the named pairing decoder `T ↦ circleLimitDecoder q (fun i n S => S (psi i n)) T`.
- `continuous_circleAverage_pair` (:60): joint continuity in (radius, centre) of the circle average of a continuous `u`.
- `continuous_circleAverage_domain` (:70), `circleAverageFun` (:75), `circleAverageFun_apply` (:78, `rfl`):
  `Ucirc u (p) = Real.circleAverage u p.val.2 p.val.1` as a `C(CircleDomain, ℝ)`.
- `continuous_circleDMSShift` (:83): continuity of the literal shift formula (`Continuous.log` on
  `max(r, ‖c - z‖) > 0`, `continuous_circleAverage_logMaxOne`).
- `circleDMSShiftFun` (:96), `circleDMSShiftFun_apply` (:100, `rfl`): `G(γ, z, F)` with the literal formula
  `p ↦ F p - γ log max(r, ‖c - z‖) + γ ⨍_{∂B_r(c)} logMaxOne`.
- `circleCompatPsi_apply` (:106): kernel form of `psi i n` through `circleMollifier_eq`.
- `isTestFunction_circleCompatPsi` (:115): each `psi i n` is a test function on `Set.univ`.
- `integrable_circleCompat_mul` (:121), `tendsto_circleCompat_mul` (:130): `mollified_continuous_circle_limit`
  (MollifiedContinuousCircleLimit.lean:105) along `eps i → 0⁺`.
- `integrable_circleCompat_dms` (:139), `tendsto_circleCompat_dms` (:148): `mollified_log_circle_limit`
  (MollifiedLogCircleLimit.lean:368) along `eps i → 0⁺`; `Filter.Tendsto.congr` passes from the kernel form to `psi`.
- `circleCompatDecoder_valid` (:160), `circleCompatDecoder_invalid` (:168): `circleLimitDecoder_of_tendsto`,
  `circleLimitDecoder_of_not_exists`.
- `circleCompatDecoder_spec` (:178): pairing-measurability (`exists_measurable_circle_limit_decoder_pairing`), valid and
  invalid characterizations, and uniqueness (`circleLimitDecoder_unique`).
- `circleCompat_addition` (:211): under the single baseline premise `n ↦ T (psi i n) → F (q i)` for all `i`:
  `D T = F`; for every continuous `u`, `v ↦ u v * psi i n v` is integrable and `D (T + ∫ u φ) = F + circleAverageFun u hu`;
  for every `γ`, `z`, `v ↦ dmsShift γ z v * psi i n v` is integrable and `D (T + ∫ dmsShift γ z φ) = circleDMSShiftFun γ z F`.

## Checks

- `lc` (compiled with warnings as errors): CHECK OK.
- `lb HarmonicBalls.Proofs.Sec11.ClosureScales.CircleDecoderAdditionCompatibility`: BUILD OK.
- Raw scan of the file for `sorry`, `axiom`, `admit`, `native_decide`, `maxHeartbeats`: 0 hits (so the comment-aware
  scan is also clean).
- `#print axioms` for the 14 declarations above, from a scratch file outside the repository
  (`/tmp/z3-axcheck/AxCheck.lean`): each depends on exactly `propext`, `Classical.choice`, `Quot.sound`.

## Decisions

1. The joint continuity of the circle average is re-proved locally by the parametric-integral argument of
   `Section6.continuous_circleAverage_radius_center` (`Proofs/Sec6/ContinuousWeylCircleAverage.lean:17`). Importing that
   module instead pulls 182 modules into the closure, including `LatticeProb.Prob.Birkhoff` (the Lattice-Probability port),
   which would create a credit obligation.
2. `circleAverageFun` and `circleDMSShiftFun` carry their continuity proofs in the definition, so the conclusions are
   equalities in `C(CircleDomain, ℝ)` with the literal formulas.
3. The additions are written literally as `∫ v : ℂ, u v * φ v` and `∫ v : ℂ, dmsShift γ z v * φ v`. No linearity or
   algebraic property of `T` is used; `T` is an arbitrary `(ℂ → ℝ) → ℝ`.
4. Kernel bridge: `circleMollifier` uses `(e ^ 2) ^ (-1 : ℤ)` and `e ^ (-1 : ℤ)`, whereas `mollified_log_circle_limit`
   uses `((e) ^ 2)⁻¹` and `e⁻¹`. The bridge is `circleMollifier_eq` (through `mollifierAt`), not a zpow rewrite.
   `mollified_continuous_circle_limit` already uses the `circleMollifier` kernel and needs no bridge.

## Open items for the operator

- The file depends on `HarmonicBalls.dmsShift` (`Proposed/DuplantierMillerSheffield.lean:34`), which is pending operator
  source-check (DMS Lemma A.10, whole-plane clause, arXiv:1409.7055v4). It is used as a definition only; no proposition
  of that file is used.
- Not claimed here: the decoder equals the circle profile on the conull event (r10 identification); the countable
  Gaussian event that supplies the baseline premise (separate task); anything touching `RawToProfileStep`,
  `CanonicalProfile` (E56 ruling pending); metric moments or Pfeffer Def1.6 / Prop4.6.
