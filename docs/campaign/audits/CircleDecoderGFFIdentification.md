# Audit: CircleDecoderGFFIdentification (task sec11-circle-decoder-gff-identification)

Module: `HarmonicBalls/Proofs/Sec11/ClosureScales/CircleDecoderGFFIdentification.lean` (new, 149 lines; round 34: rename, see Checks).
Source: r10 written proof, `notes/sec11-proof/sec11-proof-r10.tex` lines 1313-1350 (the Borel decoder on the conull
event, the continuous addition, the logarithmic insertion). Audited at the ROUND-9 TEX ranges `l:r9-circle-code`, lines
1313-1350 of that file (sub-ranges as recorded in `BorelCircleLimitDecoder.md`, `MollifiedContinuousCircleLimit.md` and
`MollifiedLogCircleLimit.md`). The former citation `AUDIT-r9.md` 931-998 was a Markdown line range of a 157-line file and
is withdrawn. Reaffirmed in `AUDIT-r10.md` 110; that line reference could not be re-located in `~/paper-fleets/hb` or
`~/fleet` in round 34.

## Scope

Probabilistic identification of the named decoder `D = circleCompatDecoder rho q (countableCircleScale hρ q)` on
`C(CircleDomain, ℝ)`, for every whole-plane GFF `IsWholePlaneGFF P hC hcirc`, together with its deterministic
compatibility with continuous additions and with DMS shifts. Not claimed: simultaneous raw-test linearity or
representation, H^-2 reconstruction, old full-function profile equality, coded Palm consumer repair, physical exponent,
numbered result. Existing E56 `RawToProfileStep` is untouched (ruling pending).

## Statement (`HarmonicBalls.circleCompatDecoder_gff_identification`, line 64)

Fixed before any probability space: `rho`, `hρ : IsLiteralMollifier rho`, `{I : Type*} [Countable I]`, `q`,
`hq : DenseRange q`. Deterministic conjuncts (no ω): (a) scales positive, `StrictAnti`, tending to `0` in `𝓝[>] 0`
(`countableCircleScale_spec`); (b) `Integrable (u · ψ_{i,n})` for every continuous `u`
(`integrable_circleCompat_mul`); (c) `Integrable (dmsShift γ z · ψ_{i,n})` (`integrable_circleCompat_dms`); (d) `D` is
pairing-measurable (`circleCompatDecoder_spec`, first conjunct).

Probabilistic conjuncts, for every `{Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC} {hcirc}` and
`hgff : IsWholePlaneGFF P hC hcirc`: (e) `ω ↦ D (hC ω)` is measurable; (f) there is `S` measurable with `P Sᶜ = 0`
such that for every `ω ∈ S`:
(1) `∀ p : CircleDomain, D (hC ω) p = hcirc ω p.val.1 p.val.2`;
(2) `∀ u (hu : Continuous u), D (fun φ => hC ω φ + ∫ u φ) = D (hC ω) + circleAverageFun u hu`;
(3) `∀ γ z, D (fun φ => hC ω φ + ∫ dmsShift γ z φ) = circleDMSShiftFun γ z (D (hC ω))`;
(4) `∀ γ z, ‖z‖ ≤ 1 → D (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) = circleDMSShiftFun γ z (D (hC ω))`.

The raw-circle conclusion (1) concerns `CircleDomain` only. All of (2)-(4) quantify over every addition after `ω ∈ S`,
so sample-dependent `u` and `z` are covered by the same event.

## Proof route (line numbers in the new file)

1. `hCm` (line 101): `hC` is measurable into `pairingMeasSpace` by `measurable_pairing_of_eval` applied to
   `hgff.measurable_pairing` (`PalmPairingMeasurable.lean:30`). Then (e) is `(circleCompatDecoder_spec).1.comp hCm`.
2. The event. `countableCircleScale_ae_convergence` (`CountableMollifiedCircleConvergence.lean:303`, commit 4ef500f)
   gives `S₀` measurable, `P S₀ᶜ = 0`, and convergence of `hC ω (circleMollifier … (countableCircleScale hρ q i n))`
   to `hcirc ω (q i).val.1 (q i).val.2` for all `ω ∈ S₀` and all `i`. `exists_measurable_superset_of_null` applied to
   `ae_iff.mp hgff.ae_continuousOn_circle` and `ae_iff.mp hgff.ae_circleAverage_one_zero` gives measurable null
   supersets `t₁`, `t₂`. Take `S := S₀ ∩ t₁ᶜ ∩ t₂ᶜ`; `P Sᶜ = 0` by `measure_union_null`.
3. On `ω ∈ S`: `hcont` (continuity of `hcirc ω` on `Ioi 0 ×ˢ univ`) and `h10 : hcirc ω 1 0 = 0`. The restriction
   `F : C(CircleDomain, ℝ)` with `F p = hcirc ω p.val.1 p.val.2` is continuous by `hcont.comp_continuous
   continuous_subtype_val`. Convergence `hT` holds because `circleCompatPsi` unfolds to `circleMollifier`.
4. `circleCompatDecoder_valid` (`CircleDecoderAdditionCompatibility.lean:160`) gives `D (hC ω) = F`, hence (1).
5. `circleCompat_addition` (`CircleDecoderAdditionCompatibility.lean:211`, commit 6a995d2) with `T = hC ω`, `F`, gives
   (2) and (3) after rewriting `D (hC ω) = F`, and the integrability conjuncts.
6. (4): `dmsConstant γ z (hcirc ω 1 0) = 0` because `hcirc ω 1 0 = 0` and `circleAverage (dmsShift γ z) 0 1 = 0`
   for `‖z‖ ≤ 1`; so `dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)` equals `fun φ => hC ω φ + ∫ dmsShift γ z φ`, and
   (3) applies. The constant term is killed on the single event `t₂ᶜ`; no intersection over `z` is needed.

## Declarations

- `circleAverage_dmsShift_unit_sec11` (private, line 34): unit-circle average of the DMS shift vanishes for `‖z‖ ≤ 1`.
- `circleCompatDecoder_gff_identification` (line 64): main theorem, as above.

## Reuse and deviations (read these)

- `PalmDMSConstant.circleAverage_dmsShift_unit` is NOT imported, to keep this import closure light (21 modules).
  Collision account: before task `sec11-circle-palm-helper-import-integration` (HEAD 07bad1f and earlier), importing
  `PalmDMSConstant` together with `CountableMollifiedCircleConvergence` was rejected by Lean, because
  `HarmonicBalls.circleAverage_log_norm_sub_eq_log_max` was declared twice: in `Proofs/Sec8/CircleLogPotential.lean:17`
  (imported by `PalmDMSConstant`) and in `Proofs/Sec11/ClosureScales/CirclePotential.lean:19` (imported by the
  countable-scales module). The Section 8 declaration takes the centre and point as explicit `(z x)`, the Section 11
  one as implicit `{c a}`. Resolved by moving the Section 11 declaration into the namespace
  `HarmonicBalls.CirclePotential` (same type and proof; the Section 8 declaration and its consumers are unchanged);
  the combined-import check is `docs/campaign/audits/Sec11CirclePalmImportChecks.md`. The unit-circle lemma is still
  repeated privately here against the `CirclePotential` version, now only to keep the import closure light; `PalmDMSConstant`
  is still not added. No operator ruling is needed for this rename.
- `dmsShift`, `dmsConstant`, `dmsShiftedPairing` (`Proposed/DuplantierMillerSheffield.lean:34,39,44`) are used as
  definitions only. No proposition of that file is used.
- No literature input, no new hypothesis, no admission. The hypotheses are only `IsLiteralMollifier rho`,
  `Countable I`, `DenseRange q` and `IsWholePlaneGFF`. Raw circle continuity is a field of the frozen structure
  (`Defs/GFF.lean:108`); `ae_circleAverage_one_zero` is a theorem of `Defs/GFF.lean:195`.

## Credit

Import closure of the new module: 21 HarmonicBalls modules including itself, no non-Mathlib package, no `LatticeProb`
module and no `Proofs/Sec8` module. Leonardo Bonanno's Lattice-Probability code is therefore not consumed, and no credit
line is required. The header records this and the reason for the omitted import.

## Checks

- `lc`: CHECK OK (`HarmonicBalls/Proofs/Sec11/ClosureScales/CircleDecoderGFFIdentification.lean`), 0 warnings.
- `lb HarmonicBalls.Proofs.Sec11.ClosureScales.CircleDecoderGFFIdentification`: BUILD OK.
- Raw scan `sorry|axiom|admit|native_decide|maxHeartbeats|set_option`: 0 hits.
- Comment-aware scan (block and line comments removed) for the same tokens plus `extern|implemented_by|unsafe`: 0 hits.
- `#print axioms HarmonicBalls.circleCompatDecoder_gff_identification`: `[propext, Classical.choice, Quot.sound]`.
- Round 34 (task `sec11-circle-palm-helper-import-integration`, after the rename of the Section 11 helper): `lc` CHECK OK
  for `CirclePotential`, `MollifiedLogCircleLimit`, `CircleTestFubiniLimit` and this module (only the helper qualification
  at line 51 changed here; the decoder identification statement and proof are unchanged). Combined-import check:
  `docs/campaign/audits/Sec11CirclePalmImportChecks.md`.
