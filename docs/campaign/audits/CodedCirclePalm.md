# Coded circle Palm consumers on the actual carrier `C(CircleDomain, ℝ)` (audit)

Task: `e56-actual-circle-coded-palm-consumers`. Source: `notes/sec11-proof/sec11-proof-r8.tex` lines 1783-1816
(marked identity and eq:r6-palm, line 1815); the actual carrier and the countable measurable decoder are
`notes/sec11-proof/sec11-proof-r10.tex` lines 927-950 and 1257-1392; the marked identity on the actual carrier is at
lines 2575-2778. Scope: the two Palm consumers of Route (A) are re-derived on the actual carrier, with `RawToProfileStep`
removed from their hypotheses. Out of scope: `StepM` (the genuine staged DMS input, still an explicit hypothesis),
the numbered results, and any frozen declaration.

## Lean files

- `HarmonicBalls/Proofs/Sec11/ClosureScales/CodedCirclePalm.lean` (new). The actual-carrier coded measure
  `circleProfileMeasure`, its dyadic ingredients `circleRadiusField`, `circleProfileApprox`, `circleGoodProfiles`,
  `circleProfileLimit`, `circleProfileFunctional`, the internal adapter `circleAdapter`, the factorization
  `profileMeasure_eq_of_eq_on_circleIndexSet`, the characterization `circleProfileMeasure_eq`, measurability, the
  actual profile `circleCodedProfile`, and `ae_lqgMeasure_eq_circleProfileMeasure`.
- `HarmonicBalls/Proofs/Sec11/ClosureScales/PalmStepM.lean`. `StepM` and `RawToProfileStep` kept verbatim. Real
  Ω-consumer `palm_circle_omega_of_stepM`. Quarantined `palm_omega_of_stepM_stepB_quarantined` (historical, unchanged body).
- `HarmonicBalls/Proofs/Sec11/ClosureScales/PalmLambdaMeasurable.lean`. Real λ-consumer
  `eq_r6_palm_circle_lambda_of_stepM`. Quarantined `eq_r6_palm_lambda_of_stepM_stepB_quarantined`.

## Statements (binders as in the files)

- `circleProfileMeasure (γ α₀ : ℝ) (F : C(CircleDomain, ℝ)) : Measure ℂ := RealRMK.rieszMeasure (circleProfileFunctional γ α₀ F)`.
  `circleProfileApprox γ α₀ k F := profileDecoder γ (dyadicScale k) (circleRadiusField α₀ F k)` with
  `circleRadiusField α₀ F k z := F ⟨(dyadicScale k, z), _⟩ - α₀ * Real.circleAverage (fun x => Real.log ‖x‖) z (dyadicScale k)`
  (the dyadic instance of `fieldCircleAverage`, Defs/GFF.lean:118).
- Characterization `circleProfileMeasure_eq γ α₀ F : circleProfileMeasure γ α₀ F = profileMeasure γ α₀ (circleAdapter F)`.
  `circleAdapter F` is the zero-off-`CircleDomain` extension, an internal proof device (not a carrier; no public
  statement reads it off `CircleDomain`).
- Factorization `profileMeasure_eq_of_eq_on_circleIndexSet`: canonical profiles agreeing on `circleIndexSet` have equal
  `profileMeasure` (the independence of the extension).
- `circleCodedProfile hρ q T := circleCompatDecoder rho q (countableCircleScale hρ q) T`, with `hρ : IsLiteralMollifier rho`
  and `q : I → CircleDomain`.
- `ae_lqgMeasure_eq_circleProfileMeasure`: `IsLQGMeasureOfField P γ 0 hcirc μ` and `F ω p = hcirc ω p.1.1 p.1.2` a.s.
  for all `p : CircleDomain` give `μ ω = circleProfileMeasure γ 0 (F ω)` a.s.
- `palm_circle_omega_of_stepM`: hypotheses `hG : IsWholePlaneGFF P hC hcirc`, `hμ : IsLQGMeasureOfField P γ 0 hcirc μ`,
  `hM : StepM P γ hC hcirc μ`, `hρ : IsLiteralMollifier rho`, `q : I → CircleDomain` with `hq : DenseRange q`,
  `Ψ : C(CircleDomain, ℝ) → ℂ → ℝ≥0∞` measurable on the product. Conclusion:
  `∫⁻ ω, ∫⁻ z in ball 0 1, Ψ (F ω) z ∂(circleProfileMeasure γ 0 (F ω)) ∂P = ∫⁻ z in ball 0 1, ∫⁻ ω, Ψ (circleDMSShiftFun γ z (F ω)) z ∂P ∂volume`,
  with `F ω = circleCodedProfile hρ q (hC ω)`.
- `eq_r6_palm_circle_lambda_of_stepM`: the same hypotheses; the λ-form with `λ = Measure.map (fun ω => F ω) P`.

## Route and inputs

- Decoder: `circleCompatDecoder_gff_identification` (CircleDecoderGFFIdentification.lean:67). Its clause 6 gives
  measurability for `pairingMeasSpace`; clause 7 gives `Measurable (fun ω => F ω)` and, on a conull set `S`, the
  circle-field identification `F ω p = hcirc ω p.1.1 p.1.2` and the DMS compatibility
  `F (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) = circleDMSShiftFun γ z (F ω)` for `‖z‖ ≤ 1`.
- `StepM` is the only staged input. `RawToProfileStep` is not used by any new declaration.
- Canonical input: `profileMeasure_ae_eq` (LQGProfileMeasureAE.lean:58) and `measurable_profileMeasure`
  (LQGProfileMeasurable.lean:155).
- Shift: `measurable_circleDMSShiftFun_fixedGamma` (CircleShiftContinuity.lean:114).

## Quarantine and naming

- `RawToProfileStep` (PalmStepM.lean) is kept verbatim, as the operator required. The canonical consumers that take it
  are renamed `palm_omega_of_stepM_stepB_quarantined` and `eq_r6_palm_lambda_of_stepM_stepB_quarantined`, with
  unchanged bodies, as historical evidence only. No new declaration uses them.
- The two generic kernel lemmas `measurable_lintegral_kernel_of_pointwise_finite` and
  `measurable_lintegral_indicator_const_of_pointwise_finite` are moved unchanged from PalmLambdaMeasurable.lean to
  CodedCirclePalm.lean, so that both carriers use them.
- Downstream: before the change, no file outside PalmStepM.lean and PalmLambdaMeasurable.lean used the consumer names
  (grep over `HarmonicBalls` and `docs`). PalmStepMDMS.lean and PalmTotalMass.lean import PalmStepM but do not use the
  changed names.

## Import closure and credit

- `CircleDecoderGFFIdentification` and `CircleShiftContinuity`: no `LatticeProb` import (checked by a transitive
  import walk). `LQGProfileMeasurable` and `LQGProfileMeasureAE` import six `LatticeProb.Bonanno.LQGMetric.Field.*`
  modules (CircleAvgBridge, CircleAvgGP, CircleAvgKolm, ExistGFF, MarkovGermVerPot, MarkovNorm). Hence
  CodedCirclePalm.lean, PalmStepM.lean and PalmLambdaMeasurable.lean carry the credit line to Leonardo Bonanno. The
  credit was missing from PalmStepM.lean before this task, although its closure already contained these imports.
- `Proposed.DuplantierMillerSheffield` enters through CircleDecoderGFFIdentification and PalmStepM, for the definitions
  `dmsShift`, `dmsConstant`, `dmsShiftedPairing` only; no Proposed statement is assumed.

## Checks

- Lock-free compile check (`lc`, warnings are errors), all CHECK OK: CodedCirclePalm.lean (log 040136-898036),
  PalmStepM.lean (040429-1212716), PalmLambdaMeasurable.lean (040724-1549308), PalmStepMDMS.lean (040756-1611289),
  PalmTotalMass.lean (040829-1685452), Audit/Sec11CirclePalmImportChecks.lean (040851-1726585).
- Module builds (`lb`), BUILD OK: CodedCirclePalm (040251-1029613), PalmStepM (040537-1338314), PalmLambdaMeasurable
  (040756-1611099), and the combined audit module `HarmonicBalls.Audit.Sec11CirclePalmImportChecks` (imports the root
  `HarmonicBalls`), BUILD OK (042508-3442438).
- Axioms: probe `scratch/z3probe/PalmProbe.lean` prints `#print axioms` for `palm_circle_omega_of_stepM`,
  `eq_r6_palm_circle_lambda_of_stepM`, `circleProfileMeasure_eq`, `ae_lqgMeasure_eq_circleProfileMeasure`,
  `profileMeasure_eq_of_eq_on_circleIndexSet`, `measurable_circle_palm_lintegral` and the two quarantined consumers. The
  probe compiled (log 040941-1827194). All eight printed lists are exactly `[propext, Classical.choice, Quot.sound]`.
- Raw scan of the three Lean files: no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `extern`, `maxHeartbeats`,
  `set_option`, `implemented_by`, `opaque`, `partial`: 0 hits.
- Credit: each of the three Lean files carries one line crediting Leonardo Bonanno (count 1 per file).
