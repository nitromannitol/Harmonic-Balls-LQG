# Audit: Sec11CirclePalmImportChecks (task sec11-circle-palm-helper-import-integration)

Module: `HarmonicBalls/Audit/Sec11CirclePalmImportChecks.lean` (new, 85 lines; namespace `HarmonicBalls.Audit.Sec11CirclePalm`).
Purpose: one file imports `HarmonicBalls`, `PalmStepMDMS` (hence `PalmDMSConstant` and the Section 8 circle potential) and
`CircleDecoderGFFIdentification` (hence the Section 11 circle decoder and potential). It checks that the two circle-average
helpers coexist under distinct names and that the typed references have the stated types. It adds no mathematics and
claims no numbered result.

Credit. The union import closure of this file (949 modules) contains Leonardo Bonanno's Lattice-Probability formalization:
12 `LatticeProb` modules, among them `LatticeProb.Prob.Birkhoff`, reached through `Proofs/Sec8/CircleLogPotential.lean`.
It is used exclusively through the pinned Lattice-Probability port, `nitromannitol/Lattice-Probability` at revision
`3912597a70dcc6c9b73042abd884a26989341c8d` (`lake-manifest.json`). This check adds no Lattice-Probability code.

## The collision and its repair

- Before (HEAD 07bad1f): importing `Proofs/Sec8/CircleLogPotential` and then `Proofs/Sec11/ClosureScales/CirclePotential`
  fails with `import HarmonicBalls.Proofs.Sec11.ClosureScales.CirclePotential failed, environment already contains
  'HarmonicBalls.circleAverage_log_norm_sub_eq_log_max' from HarmonicBalls.Proofs.Sec8.CircleLogPotential`
  (lc log `logs/lc/212533-3274161.log`).
- Repair (namespace only): the Section 11 declaration is now `HarmonicBalls.CirclePotential.circleAverage_log_norm_sub_eq_log_max`
  (`CirclePotential.lean:24`); its type and proof are unchanged. The Section 8 declaration
  `HarmonicBalls.circleAverage_log_norm_sub_eq_log_max` (`CircleLogPotential.lean:17`) and all Section 8 consumers are untouched.
- Section 11 consumers now use the qualified name: `MollifiedLogCircleLimit.lean:157`, `CircleTestFubiniLimit.lean:471-472`,
  `CircleDecoderGFFIdentification.lean:51`.
- Grep check: every Section 11 occurrence of the helper is qualified. The one unqualified occurrence under `Proofs/Sec11/`,
  `PalmDMSConstant.lean:40` (`circleAverage_log_norm_sub_eq_log_max one_pos 0 z`), is a Section 8 consumer: it imports
  `Proofs/Sec8/CircleLogPotential` and uses the Section 8 argument order. It is untouched and resolves to the Section 8
  declaration by design.

## Typed references (`HarmonicBalls/Audit/Sec11CirclePalmImportChecks.lean`)

| Theorem | Refers to | Hypotheses kept |
|---|---|---|
| `circleAverage_log_norm_sub_eq_log_max_sec8` (l.27-32) | `HarmonicBalls.circleAverage_log_norm_sub_eq_log_max` (Section 8) | `(hr : 0 < r) (z x : ℂ)`, explicit |
| `circleAverage_log_norm_sub_eq_log_max_sec11` (l.34-38) | `HarmonicBalls.CirclePotential.circleAverage_log_norm_sub_eq_log_max` (Section 11) | `{c a : ℂ} {r : ℝ} (hr : 0 < r)`, implicit |
| `stepM_of_dms_typed` (l.40-46) | `HarmonicBalls.stepM_of_dms` (`PalmStepMDMS.lean:30`) | conditional on `hU : DMSLemmaA10WholePlaneUnnormalized ...`; conclusion `StepM P γ hC hcirc μ` |
| `circleCompatDecoder_gff_identification_typed` (l.48-78) | `HarmonicBalls.circleCompatDecoder_gff_identification` (`CircleDecoderGFFIdentification.lean:64`) | `IsLiteralMollifier rho`, `Countable I`, `DenseRange q`; `IsWholePlaneGFF` inside the last conjunct |

The decoder statement is copied verbatim from the module by script (the local copy's lines 67-94), so the typed copy cannot
drift from the source. Its proof is `HarmonicBalls.circleCompatDecoder_gff_identification rho hρ q hq`.

## Results

- `lc`: CHECK OK for the audit module, `CirclePotential`, `MollifiedLogCircleLimit`, `CircleTestFubiniLimit` and
  `CircleDecoderGFFIdentification`.
- `lb HarmonicBalls.Audit.Sec11CirclePalmImportChecks`: BUILD OK (10340 jobs; log `logs/lb/213024-3289855.log`). The
  warnings in that log come from the Lattice-Probability package; none come from the owned files.
- `lb HarmonicBalls.Proofs.Sec11.ClosureScales.CirclePotential`: BUILD OK.
- `#print axioms` (log lines 82-85): each of the four typed theorems depends on `[propext, Classical.choice, Quot.sound]`.
- Raw word scan for `sorry|admit|native_decide|axiom` over the five owned Lean files: 0 hits. The substring scan hits only
  the four `#print axioms` lines.
- Comment-aware scan (block and line comments removed, plus `extern|implemented_by|unsafe`): 0 hits.

## Import closures (computed with the import graph)

- Audit module (union of its imports, root `HarmonicBalls` included): 949 modules; 12 `LatticeProb` modules; 127 Section 8 modules.
- `CirclePotential` (1 module), `MollifiedLogCircleLimit` (12), `CircleDecoderGFFIdentification` (21),
  `CircleTestFubiniLimit` (13): no non-Mathlib, non-HarmonicBalls import, so none consumes Lattice-Probability code and none
  needs the credit line.

## Not claimed; stale references outside this task's ownership (flagged, not edited)

- No numbered result. The StepM export stays conditional on `DMSLemmaA10WholePlaneUnnormalized` (a `Proposed` input, pending
  operator source-check). The decoder identification keeps its hypotheses.
- `RawToProfileStep`, the coded-Palm carrier and the E56 ruling are untouched.
- These audit notes still name the helper without the qualification and state the collision as open:
  `CircleTestFubiniLimit.md` lines 63, 70 and 75; `MollifiedLogCircleLimit.md` line 48; `MollifiedCircleGaussianL2.md` line 51.
  They are outside this task's OWNS list and were not edited.
- The citation `AUDIT-r10.md` 110 in `CircleDecoderGFFIdentification.md` could not be re-located in this round.
