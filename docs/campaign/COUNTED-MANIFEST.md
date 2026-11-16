# Numbered results: source inventory and audit status

This inventory is in progress. It does not certify a numbered result, authorize a frozen declaration, or count proofs. `OPEN` means the indicated check remains incomplete; `NOT YET CHECKED` is not a finding of absence. The candidate and provenance columns are leads requiring source, binder, definition and use checks.

Source: `paper/lqg_harmonic_ball-corrected.tex`, SHA-256 `e3ed40660ed77327b991b2463b599cc2a56426fff8819a57b3f4c441c2680b15`. This inventory contains 78 results and six definitions, including Lemmas 11.18–11.24. Lines refer to that source. The original inventory and its detailed historical receipts are available in Git at commit `3e2bc627e10ffa351cb541b5f2dbde80fd5b497f` for this same path.

The source, binder, definition, consumer and transitive verdicts below are independent. A blank or unexamined cell does not imply success. Kind labels and legacy candidates are preliminary; a cited proof input and the paper’s own result may coexist in one row. All candidate binder and axiom checks are NOT YET CHECKED except where stated explicitly below.

| Number | Source environment and line | Source label | Preliminary provenance | Candidate declaration and file (unchecked) | Source | Binder | Definition | Consumer | Transitive | Paper citation in proof |
|---|---|---|---|---|---|---|---|---|---|---|
| 1.1 | theorem :156 | theorem:harmonic-balls | paper-owned | firstPass_1_1 @ HarmonicBalls/FirstPass/S1S10.lean:35 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 1.2 | theorem :174 | theorem:harmonic-balls-properties | paper-owned | firstPass_1_2 @ HarmonicBalls/FirstPass/S1S10.lean:43 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 1.3 | prop :183 | prop:locally-determined | paper-owned | firstPass_1_3 @ HarmonicBalls/FirstPass/S1S10.lean:53 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 2.1 | fact :407 | fact:lqg-measure | cited:Duplantier-Sheffield 2011 Prop 2.1 and Sheffield-Wang 2016 (conformal covariance); I-III from the limit eq:measure-lim | NOT YET CHECKED | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 2.2 | fact :438 | fact:lqg-metric | cited:Ding-Dubedat-Dunlap-Falconet 2020, Dubedat-Falconet-Gwynne-Pfeffer-Sun 2020, Gwynne-Miller 2021 (no theorem numbers printed) | NOT YET CHECKED | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 2.3 | prop :486 | prop:green-properties | paper-owned (standard; no printed proof) | closure_2_3 @ HarmonicBalls/FirstPass/Closure.lean:112 | MISMATCH: positivity excludes pole | OPEN | MISMATCH: zero at pole; source extended-valued representation not yet checked | OPEN | OPEN | NOT YET CHECKED |
| 2.4 | lemma :503 | lemma:volume-growth | cited:Berestycki-Gwynne 2020 Lemma A.1 (argument adapted, no printed proof of eq:ball-volume); eq:ann-volume derived in the paper | PROOFS liouvilleVolumeGrowthStmt_of_existence @ HarmonicBalls/Proofs/Sec9/LQGExistenceConsequences.lean:30 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 2.5 | prop :530 | prop:lbm-exit-time | paper-owned (proof sketch: Campanato embedding, Ponce 2016 Sec 16.2 / remark after Prop 13.5) | Green clause: greenPotentialHolderStmt_holds @ HarmonicBalls/FirstPass/Phase2/GreenPotentialHolderHolds.lean:24; full LBM clause OPEN | OPEN | Green clause outer type checked | OPEN | Two Green uses checked; full OPEN | OPEN | NOT YET CHECKED |
| 2.6 | prop :560 | prop:lbm-continuity | cited:Kigami 2019 Thm 13.1 (input Lemma 2.4; scaling from the unit square) | NOT YET CHECKED | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 3.1 | lemma :627 | lemma:basic-properties | paper-owned (proved in App A: Lemma A.1) | closure_3_1 @ HarmonicBalls/FirstPass/Closure.lean:133 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 3.2 | lemma :633 | lemma:non-coincidence-open-harmonic | paper-owned (proved in App A: Lemmas A.1-A.2; nu>=0 not proved) | closure_3_2 @ HarmonicBalls/FirstPass/Closure.lean:136 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 3.3 | lemma :651 | lemma:monotonicity | paper-owned (proved in App A: Lemma A.3) | closure_3_3 @ HarmonicBalls/FirstPass/Closure.lean:139 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 3.4 | lemma :657 | lemma:conservation-of-mass | paper-owned (proved in App A: Lemmas A.4-A.5) | closure_3_4 @ HarmonicBalls/FirstPass/Closure.lean:142 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 3.5 | lemma :666 | lemma:cluster-compatibility | paper-owned (proved in App A: Lemma A.6) | closure_3_5 @ HarmonicBalls/FirstPass/Closure.lean:145 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 4.1 | prop :682 | prop:lower-bound | paper-owned | closure_4_1 @ HarmonicBalls/FirstPass/Closure/SecA45.lean:73 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 4.2 | lemma :731 | odometer:cont | paper-owned | closure_4_2 @ HarmonicBalls/FirstPass/Closure/SecA45.lean:76 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 4.3 | lemma :765 | lemma:harmonic-ball | paper-owned | closure_4_3 @ HarmonicBalls/FirstPass/Closure/SecA45.lean:79 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 5.1 | prop :825 | prop:upper-bound | paper-owned (proved in Sec 7, line 2101, from Prop 7.1) | closure_5_1 @ HarmonicBalls/FirstPass/Closure/SecA45.lean:116 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 5.2 | prop :835 | prop:continuity | paper-owned (proved in Sec 7, line 2101, from Props 7.1, 7.2) | closure_5_2_derivedInputs19 @ HarmonicBalls/FirstPass/Phase2/DerivedInputs19.lean:82 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 5.3 | prop :848 | prop:boundary-measure | paper-owned (proved in Sec 8 as Prop 8.1) | firstPass_5_3 @ HarmonicBalls/FirstPass/S5S7S8.lean:136 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 5.4 | prop :866 | prop:conditional | paper-owned (proof: text lines 846-851) | firstPass_5_4 @ HarmonicBalls/FirstPass/S5S7S8.lean:148 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 5.5 | theorem :875 | theorem:full-theorem-minus-uniqueness | paper-owned (proof: Sec 5.3, lines 951-1009) | firstPass_5_5 @ HarmonicBalls/FirstPass/S5S7S8.lean:161 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 5.6 | prop :884 | prop:uniqueness | paper-owned (proved in Sec 9, line 2415) | closure_5_6 @ HarmonicBalls/FirstPass/Closure/SecA45.lean:127 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 5.7 | lemma :897 | lemma:scale-invariance-flow | paper-owned | closure_5_7 @ HarmonicBalls/FirstPass/Closure/SecA45.lean:139 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 5.8 | lemma :1093 | lemma:strong-compatibility | paper-owned | closure_5_8 @ HarmonicBalls/FirstPass/Closure/SecA45.lean:150 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 6.1 | prop :1138 | prop:harnack-type-property | paper-owned | closure_6_1 @ HarmonicBalls/FirstPass/Closure/Sec6.lean:37 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 6.2 | prop :1151 | prop:harnack-type-stronger-property | paper-owned (with Prop 6.1 proved at line 1593 from Lemmas 6.6, 6.11) | closure_6_2 @ HarmonicBalls/FirstPass/Closure/Sec6.lean:41 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 6.3 | lemma :1242 | lemma:good-annuli | paper-owned | closure_6_3 @ HarmonicBalls/FirstPass/Closure/Sec6.lean:45 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 6.4 | lemma :1259 | lemma:annulus-hit | paper-owned | closure_6_4 @ HarmonicBalls/FirstPass/Closure/Sec6.lean:49 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 6.5 | lemma :1333 | lemma:annulus-iterate | cited:Gwynne-Miller 2020 (Local metrics of the GFF, Ann. Inst. Fourier 70), Lemma 3.1 (printed at line 1259: [Lemma 3.1]{gwynne2020local}; Lemma 6.5 is a special case) | PROOFS annulusIterationStmt_of_three_inputs @ HarmonicBalls/Proofs/Sec6/FullThreeInputAssembly.lean:72 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 6.6 | lemma :1367 | lemma:very-good-annuli | paper-owned | closure_6_6 @ HarmonicBalls/FirstPass/Closure/Sec6.lean:53 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 6.7 | lemma :1379 | lemma:very-good-annuli-hit | paper-owned | closure_6_7 @ HarmonicBalls/FirstPass/Closure/Sec6.lean:57 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 6.8 | lemma :1461 | lemma:odometer-annuli | paper-owned | closure_6_8 @ HarmonicBalls/FirstPass/Closure/Sec6.lean:62 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 6.9 | lemma :1532 | lemma:harmonic-odometer-comparison | paper-owned | closure_6_9 @ HarmonicBalls/FirstPass/Closure/Sec6.lean:67 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 6.10 | lemma :1588 | lemma:odometer-bound-lqg-mass | paper-owned | closure_6_10 @ HarmonicBalls/FirstPass/Closure/Sec6.lean:72 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 6.11 | lemma :1643 | lemma:very-good-annuli-satisfy-harnack-type-estimate | paper-owned | closure_6_11 @ HarmonicBalls/FirstPass/Closure/Sec6.lean:77 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 6.12 | lemma :1712 | lemma:shell-decomposition | paper-owned | closure_6_12 @ HarmonicBalls/FirstPass/Closure/Sec6.lean:82 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 6.13 | lemma :1787 | lemma:low-mass-implies-small-odometer | paper-owned | closure_6_13 @ HarmonicBalls/FirstPass/Closure/Sec6.lean:87 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 7.1 | prop :2038 | prop:upper-bound-polynomially-high-prob | paper-owned | closure_7_1 @ HarmonicBalls/FirstPass/Closure/Sec78910.lean:88 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 7.2 | prop :2098 | prop:continuity-of-clusters | paper-owned | firstPass_7_2 @ HarmonicBalls/FirstPass/S5S7S8.lean:52 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 8.1 | prop :2200 | prop:boundary-measure-zero | paper-owned | firstPass_8_1 @ HarmonicBalls/FirstPass/S5S7S8.lean:72 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 8.2 | lemma :2229 | lemma:mu_h-doubling-and-harnack | paper-owned | firstPass_8_2_S8d_noWeyl_derivedInputsCampbell @ HarmonicBalls/FirstPass/Phase2/CampbellCountedForms.lean:25 | OPEN | One outer mass-bound input checked | OPEN | DMS supply application checked; full OPEN | OPEN | DMS A.10 marked, source 2291; IG4 Prop 2.9, source 2297 |
| 8.3 | lemma :2238 | lemma:doubling-alpha | paper-owned | closure_8_3 @ HarmonicBalls/FirstPass/Closure/Sec78910.lean:150 | OPEN | OPEN | OPEN | OPEN | OPEN | DMS Lemma 7.2 analogous tail only, source 2270 |
| 9.1 | lemma :2363 | lemma:obstacle-comp | cited:Shahgholian-Sjodin 2013 Thm 2.1; Sakai 1984 (a complete proof is printed) | PROOFS obstacleComparison @ HarmonicBalls/Proofs/Sec9/ObstacleComparison.lean:32 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 9.2 | prop :2397 | prop:sub-harmonic-ball-uniqueness | paper-owned | NOT YET CHECKED | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 9.3 | lemma :2420 | lemma:contains-boundary | paper-owned | firstPass_9_3 @ HarmonicBalls/FirstPass/S2S3S4S9SA.lean:94 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 9.4 | lemma :2478 | lemma:regular-open-ae | paper-owned | firstPass_9_4 @ HarmonicBalls/FirstPass/S2S3S4S9SA.lean:99 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 10.1 | lemma :2580 | lemma:cannot-cross | paper-owned | firstPass_10_1 @ HarmonicBalls/FirstPass/S1S10.lean:64 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 10.2 | definition :2634 | NOT YET CHECKED | definition | IsLoop / IsArc / IsSimpleLoop / IsSimpleArc @ HarmonicBalls/Defs/Geometry.lean:82,87,92,97 | OPEN | OPEN | Body printed; correspondence OPEN | OPEN | OPEN | NOT YET CHECKED |
| 10.3 | definition :2644 | NOT YET CHECKED | definition | IsLocallyConnectedSet @ HarmonicBalls/Defs/Geometry.lean:103 | OPEN | OPEN | Body printed; correspondence OPEN | OPEN | OPEN | NOT YET CHECKED |
| 10.4 | definition :2650 | NOT YET CHECKED | definition | IsCutPoint @ HarmonicBalls/Defs/Geometry.lean:108 | OPEN | OPEN | Body printed; correspondence OPEN | OPEN | OPEN | NOT YET CHECKED |
| 10.5 | lemma :2674 | lemma:crossing-connected | paper-owned | NOT YET CHECKED | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 10.6 | prop :2783 | prop:boundary-simple-loop | paper-owned | firstPass_10_6 @ HarmonicBalls/FirstPass/S1S10.lean:92 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 10.7 | prop :2798 | prop:boundary-simple-loop-full-cluster | paper-owned | firstPass_10_7 @ HarmonicBalls/FirstPass/S1S10.lean:75 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 11.1 | definition :2881 | def:lipschitz | definition | IsLipschitzDomain @ HarmonicBalls/Defs/Geometry.lean:133 | OPEN | OPEN | Body printed; correspondence OPEN | OPEN | OPEN | NOT YET CHECKED |
| 11.2 | prop :2893 | prop:not-balls | paper-owned | firstPass_11_2.{u} @ HarmonicBalls/FirstPass/S11.lean:58 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 11.3 | definition :2899 | NOT YET CHECKED | definition | IsOpenCone / IsCone @ HarmonicBalls/Defs/Geometry.lean:144,149 | OPEN | OPEN | Body printed; correspondence OPEN | OPEN | OPEN | NOT YET CHECKED |
| 11.4 | definition :2906 | def:cone-condition | definition | SatisfiesInteriorConeCondition / SatisfiesExteriorConeCondition / SatisfiesConeCondition @ HarmonicBalls/Defs/Geometry.lean:158,163,168 | OPEN | OPEN | Body printed; correspondence OPEN | OPEN | OPEN | NOT YET CHECKED |
| 11.5 | lemma :2923 | lemma:no-exterior-cone-condition | paper-owned | firstPass_11_5.{u} @ HarmonicBalls/FirstPass/S11.lean:66 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 11.6 | lemma :2933 | lemma:harmonic-comparison-chain | paper-owned | closure_11_6_derivedInputs19 @ HarmonicBalls/FirstPass/Phase2/DerivedInputs19.lean:240 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 11.7 | lemma :2973 | lemma:mu_h-bad-and-harnack | paper-owned | firstPass_11_7.{u} @ HarmonicBalls/FirstPass/S11b.lean:70 | OPEN | OPEN | OPEN | OPEN | OPEN | DMS A.10 and IG4 via rooted transfer, source 3019 |
| 11.8 | lemma :2980 | lemma:positive-probability | paper-owned | closure_11_8 @ HarmonicBalls/FirstPass/Closure/Sec11.lean:79 | OPEN | OPEN | OPEN | OPEN | OPEN | IG4 Prop 2.9, source 3002 |
| 11.9 | prop :3091 | prop:mass-diam-gen | paper-owned | firstPass_11_9 @ HarmonicBalls/FirstPass/S11d.lean:39 | OPEN | OPEN | OPEN | OPEN | OPEN | IG4 Prop 2.9, source 3210 |
| 11.10 | lemma :3111 | lemma:mass-diam | paper-owned | firstPass_11_10_derivedInputs17 @ HarmonicBalls/FirstPass/Phase2/DerivedInputs17.lean:431 | OPEN | OPEN | OPEN | OPEN | OPEN | IG4 Prop 2.9, source 3179 |
| 11.11 | prop :3223 | prop:not-metric-balls | paper-owned | firstPass_11_11.{u} @ HarmonicBalls/FirstPass/S11.lean:110 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 11.12 | lemma :3312 | lemma:mu_h-pinch-positive-probability | paper-owned | firstPass_11_12 @ HarmonicBalls/FirstPass/S11e.lean:42 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 11.13 | lemma :3324 | lemma:mu_h-pinch-bad | paper-owned | manyPinchScales_of_corrected @ HarmonicBalls/FirstPass/Closure/Bridge12.lean:322 | OPEN | OPEN | OPEN | OPEN | OPEN | DMS A.10 marked, source 3922-3945; local Gaussian shift, 3947-3960 |
| 11.14 | lemma :3337 | lemma:geometric-event-consequence | paper-owned | closure_11_14 @ HarmonicBalls/FirstPass/Closure/Sec11.lean:138 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 11.15 | lemma :3420 | lemma:first-event-proof | paper-owned | firstPass_11_15_derivedInputs3 @ HarmonicBalls/FirstPass/Phase2/DerivedInputs3.lean:945 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 11.16 | lemma :3424 | lemma:second-event-proof | paper-owned | firstPass_11_16_of_11_17 @ HarmonicBalls/FirstPass/S11e.lean:29 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 11.17 | lemma :3428 | lemma:third-event-proof | paper-owned | NOT YET CHECKED | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 11.18 | lemma :3583 | s11-pinch:lem:massdiam | paper-owned (source proof) | pinchSecondConditionalMass_of_frozen @ HarmonicBalls/FirstPass/S11k.lean:155 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 11.19 | lemma :3712 | s11-pinch:lem:include | paper-owned (source proof) | pinchPointEvent_of_auxiliary_events @ HarmonicBalls/FirstPass/S11e/Include.lean:29 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 11.20 | lemma :3734 | s11-pinch:lem:E1 | paper-owned (source proof) | NOT YET CHECKED | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 11.21 | lemma :3772 | s11-pinch:lem:E2 | paper-owned (source proof) | NOT YET CHECKED | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 11.22 | lemma :3801 | s11-pinch:lem:E3 | paper-owned (source proof) | NOT YET CHECKED | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 11.23 | lemma :3841 | s11-pinch:lem:mixing | paper-owned (source proof) | coordinateSigmaMixing_canonical / ergodic_dilOp @ HarmonicBalls/FirstPass/S11i/MixingCanonical.lean:181,189 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| 11.24 | lemma :3999 | s11-pinch:lem:obstruction | paper-owned (source proof) | pinchPointEvent_keyhole_subset_metricBall / pinchPointEvent_outer_subset_compl_metricBall @ HarmonicBalls/Proofs/Sec11/PinchInner.lean:18; PinchOuter.lean:15 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| A.1 | lemma :4269 | lemma:appendix-basic-properties | paper-owned | closure_A_1 @ HarmonicBalls/FirstPass/Closure/SecA45.lean:37 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| A.2 | lemma :4332 | lemma:appendix-non-coincedence-open-harmonic | paper-owned | closure_A_2 @ HarmonicBalls/FirstPass/Closure/SecA45.lean:40 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| A.3 | lemma :4411 | lemma:appendix-monotonicity | paper-owned | closure_A_3 @ HarmonicBalls/FirstPass/Closure/SecA45.lean:43 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| A.4 | lemma :4452 | lemma:appendix-zero-boundary | paper-owned | closure_A_4 @ HarmonicBalls/FirstPass/Closure/SecA45.lean:46 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| A.5 | lemma :4469 | lemma:appendix-conservation-of-mass | paper-owned | closure_A_5 @ HarmonicBalls/FirstPass/Closure/SecA45.lean:49 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |
| A.6 | lemma :4533 | lemma:appendix-cluster-compatibility | paper-owned | closure_A_6 @ HarmonicBalls/FirstPass/Closure/SecA45.lean:52 | OPEN | OPEN | OPEN | OPEN | OPEN | NOT YET CHECKED |

## Additional historical candidate leads

The following table preserves the previously indexed statement names, candidates, file locations, and reported binder names. Counts were extracted from source headers and can omit included section variables; neither the counts nor the semantic correspondence has been rechecked. They are not a claim of an unconditional result. All Proposed-input expansion, consumers and axiom receipts are NOT YET CHECKED for these rows unless recorded separately below.

| Number | Draft statement | Candidate | File:line | Historical binder count (unchecked) | Historical binder names (unchecked) |
|---|---|---|---|---|---|
| 1.1 | `ExistenceUniquenessHarmonicBallsStmt` | `firstPass_1_1_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:47 | 0 | NOT YET CHECKED |
| 1.2 | `HarmonicBallNoveltyStmt` | `firstPass_1_2_derivedInputs47` | HarmonicBalls/FirstPass/Phase2/DerivedInputs47.lean:20 | 1 | hmetric |
| 1.3 | `HarmonicBallLocalSetStmt` | `closure_1_3_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:230 | 0 | NOT YET CHECKED |
| 2.3 | `GreenFunctionBallStmt` | `closure_2_3` | HarmonicBalls/FirstPass/Closure.lean:112 | 0 | NOT YET CHECKED |
| 3.1 | `LeastSupersolutionMemStmt` | `closure_3_1_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:236 | 0 | NOT YET CHECKED |
| 3.2 | `ClusterOpenLaplacianStmt` | `closure_3_2_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:242 | 0 | NOT YET CHECKED |
| 3.3 | `ClusterMonotoneStmt` | `closure_3_3_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:248 | 0 | NOT YET CHECKED |
| 3.4 | `ClusterConservationOfMassStmt` | `closure_3_4_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:254 | 0 | NOT YET CHECKED |
| 3.5 | `ClusterCompatibilityStmt` | `closure_3_5_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:260 | 0 | NOT YET CHECKED |
| 4.1 | `ClusterLowerBoundStmt` | `closure_4_1_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:266 | 0 | NOT YET CHECKED |
| 4.2 | `LeastSupersolutionHolderStmt` | `closure_4_2_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:272 | 0 | NOT YET CHECKED |
| 4.3 | `ClusterSubharmonicBallStmt` | `closure_4_3_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:278 | 0 | NOT YET CHECKED |
| 5.1 | `ClusterUpperBoundStmt` | `closure_5_1_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:284 | 0 | NOT YET CHECKED |
| 5.2 | `ClusterContinuityStmt` | `closure_5_2_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:290 | 0 | NOT YET CHECKED |
| 5.3 | `ClusterBoundaryMeasureZeroStmt` | `closure_5_3_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:296 | 0 | NOT YET CHECKED |
| 5.4 | `RegularizedClusterHarmonicBallsStmt` | `closure_5_4_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:302 | 0 | NOT YET CHECKED |
| 5.5 | `ExistenceHarmonicBallsStmt` | `closure_5_5_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:308 | 0 | NOT YET CHECKED |
| 5.6 | `UniquenessHarmonicBallsStmt` | `closure_5_6_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:314 | 0 | NOT YET CHECKED |
| 5.7 | `ClusterScaleInvarianceStmt` | `closure_5_7_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:320 | 0 | NOT YET CHECKED |
| 5.8 | `ClusterStrongCompatibilityStmt` | `closure_5_8_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:326 | 0 | NOT YET CHECKED |
| 6.1 | `HarnackTypeEstimateStmt` | `closure_6_1_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:332 | 0 | NOT YET CHECKED |
| 6.2 | `HarnackTypeComponentStmt` | `closure_6_2_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:338 | 0 | NOT YET CHECKED |
| 6.3 | `ManyGoodAnnuliStmt` | `closure_6_3_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:344 | 0 | NOT YET CHECKED |
| 6.4 | `GoodAnnulusProbabilityStmt` | `closure_6_4_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:350 | 0 | NOT YET CHECKED |
| 6.6 | `ManyVeryGoodAnnuliStmt` | `closure_6_6_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:356 | 0 | NOT YET CHECKED |
| 6.7 | `VeryGoodAnnulusProbabilityStmt` | `closure_6_7_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:362 | 0 | NOT YET CHECKED |
| 6.8 | `AnnulusMassBoundByOdometerStmt` | `closure_6_8_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:368 | 0 | NOT YET CHECKED |
| 6.9 | `OdometerHarmonicMeasureBoundStmt` | `closure_6_9_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:374 | 0 | NOT YET CHECKED |
| 6.10 | `OdometerBoundByAnnulusMassStmt` | `closure_6_10_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:380 | 0 | NOT YET CHECKED |
| 6.11 | `VeryGoodAnnulusHarnackTypeStmt` | `closure_6_11_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:386 | 0 | NOT YET CHECKED |
| 6.12 | `ShellDecompositionStmt` | `closure_6_12_derivedInputs38` | HarmonicBalls/FirstPass/Phase2/DerivedInputs38.lean:141 | 0 | NOT YET CHECKED |
| 6.13 | `LowMassSmallOdometerStmt` | `closure_6_13_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:392 | 0 | NOT YET CHECKED |
| 7.1 | `ClusterUpperBoundPolyHighProbStmt` | `closure_7_1_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:398 | 0 | NOT YET CHECKED |
| 7.2 | `ClusterTimeContinuityStmt` | `closure_7_2_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:404 | 0 | NOT YET CHECKED |
| 8.1 | `BoundaryMeasureZeroOfCompactClusterStmt` | `closure_8_1_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:410 | 0 | NOT YET CHECKED |
| 8.2 | `TypicalPointManyGoodScalesStmt` | `firstPass_8_2_S8d_noWeyl_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:73 | 0 | NOT YET CHECKED |
| 8.3 | `OriginManyGoodScalesStmt` | `closure_8_3_derivedInputs44` | HarmonicBalls/FirstPass/Phase2/DerivedInputs44.lean:70 | 0 | NOT YET CHECKED |
| 9.3 | `HarmonicBallBoundarySubsetStmt` | `firstPass_9_3_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:79 | 0 | NOT YET CHECKED |
| 9.4 | `RegularOpenEqOfAEEqStmt` | `firstPass_9_4_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:85 | 0 | NOT YET CHECKED |
| 10.1 | `ClusterBoundedCrossingsStmt` | `firstPass_10_1_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:91 | 0 | NOT YET CHECKED |
| 10.6 | `ComplementComponentBoundarySimpleLoopStmt` | `firstPass_10_6_derivedInputs46` | HarmonicBalls/FirstPass/Phase2/DerivedInputs46.lean:27 | 0 | NOT YET CHECKED |
| 10.7 | `HarmonicBallComplementBoundaryJordanStmt` | `closure_10_7_derivedInputs46` | HarmonicBalls/FirstPass/Phase2/DerivedInputs46.lean:118 | 0 | NOT YET CHECKED |
| 11.2 | `HarmonicBallNotLipschitzStmt` | `firstPass_11_2_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:111 | 0 | NOT YET CHECKED |
| 11.5 | `NoConeConditionStmt` | `firstPass_11_5_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:122 | 0 | NOT YET CHECKED |
| 11.6 | `AnnulusMassBoundByHarmonicChainStmt` | `closure_11_6_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:432 | 0 | NOT YET CHECKED |
| 11.7 | `ManyConeBadScalesStmt` | `manyConeBadScalesStmt_holds` | HarmonicBalls/FirstPass/Phase2/ConeBadScalesHolds.lean:31 | 0 | NOT YET CHECKED |
| 11.8 | `ConeBadEventProbabilityStmt` | `closure_11_8_derivedInputs43` | HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:438 | 0 | NOT YET CHECKED |
| 11.9 | `SmallMetricDiameterLargeMassStmt` | `firstPass_11_9_derived` | HarmonicBalls/FirstPass/Phase2/FieldAxiomsConsequencesDerived.lean:68 | 0 | NOT YET CHECKED |
| 11.10 | `SmallMetricDiameterLargeMassSquareStmt` | `S11c.firstPass_11_10_derived` | HarmonicBalls/FirstPass/Phase2/FieldAxiomsDerived.lean:56 | 0 | NOT YET CHECKED |
| 11.11 | `HarmonicBallNotMetricBallStmt` | `firstPass_11_11_derived` | HarmonicBalls/FirstPass/Phase2/PinchScalesSeedInputsDerived.lean:50 | 1 | h13 |
| 11.12 | `PinchEventPositiveProbabilityStmt` | `firstPass_11_12_derived` | HarmonicBalls/FirstPass/Phase2/FieldAxiomsDerived.lean:48 | 0 | NOT YET CHECKED |
| 11.13 | `ManyPinchScalesStmt` | `manyPinchScales_of_corrected` | HarmonicBalls/FirstPass/Closure/Bridge12.lean:322 | 1 | h |
| 11.14 | `PinchEventMetricBallConsequenceStmt` | `firstPass_11_14_derived` | HarmonicBalls/FirstPass/Phase2/FieldAxiomsConsequencesDerived.lean:72 | 0 | NOT YET CHECKED |
| 11.15 | `PinchFirstEventPositiveStmt` | `firstPass_11_15_derived` | HarmonicBalls/FirstPass/Phase2/FieldAxiomsConsequencesDerived.lean:76 | 0 | NOT YET CHECKED |
| 11.16 | `PinchSecondEventPositiveStmt` | `firstPass_11_16_derived` | HarmonicBalls/FirstPass/Phase2/FieldAxiomsDerived.lean:44 | 0 | NOT YET CHECKED |
| 11.17 | `PinchThirdEventPositiveStmt` | `pinchThirdEventPositiveStmt_derived` | HarmonicBalls/FirstPass/Phase2/FieldAxiomsDerived.lean:40 | 0 | NOT YET CHECKED |
| A.1 | `ObstacleLeastSuperharmonicMajorantStmt` | `closure_A_1` | HarmonicBalls/FirstPass/Closure/SecA45.lean:37 | 0 | NOT YET CHECKED |
| A.2 | `ObstacleNonCoincidenceHarmonicStmt` | `closure_A_2` | HarmonicBalls/FirstPass/Closure/SecA45.lean:40 | 0 | NOT YET CHECKED |
| A.3 | `ObstacleMonotoneStmt` | `closure_A_3` | HarmonicBalls/FirstPass/Closure/SecA45.lean:43 | 0 | NOT YET CHECKED |
| A.4 | `ObstacleOdometerZeroBoundaryStmt` | `closure_A_4` | HarmonicBalls/FirstPass/Closure/SecA45.lean:46 | 0 | NOT YET CHECKED |
| A.5 | `ObstacleConservationOfMassStmt` | `closure_A_5` | HarmonicBalls/FirstPass/Closure/SecA45.lean:49 | 0 | NOT YET CHECKED |
| A.6 | `ObstacleCompatibilityStmt` | `closure_A_6` | HarmonicBalls/FirstPass/Closure/SecA45.lean:52 | 0 | NOT YET CHECKED |

## Checked declarations and remaining questions

- `HarmonicBalls.Closure.closure_6_1.{u}` elaborates with three leading inputs, respectively `∀ Ω [MeasurableSpace Ω] P γ hC hcirc, WholePlaneLQGBallMassBounds P γ hC hcirc`, `∀ Ω [MeasurableSpace Ω] P γ hC hcirc, LQGMeasureCoordChange P γ 0 hC hcirc`, and `∀ Ω [MeasurableSpace Ω] P γ α hC hcirc, LQGMeasureExistence P γ α hC hcirc`; its conclusion is `HarnackTypeEstimateStmt`. The historical header-based zero count is incomplete. Source, full expansion, consumers and axioms for this declaration remain OPEN.
- `HarmonicBalls.greenPotentialHolderStmt_holds.{u} : GreenPotentialHolderStmt.{u}` has no outer premises. Its direct source check has no warnings, and its axiom set is `[propext, Classical.choice, Quot.sound]`. Two exact typed uses in `FirstPass/Phase2/DerivedInputs44.lean:34-39,69-73` and their standard axioms were checked. This addresses only the Green-potential clause of 2.5, not its LBM assertion. The binder review of that clause is provisional pending standing-definition review. General-domain identification with the killed-Brownian occupation kernel, normalization, the paper’s smooth-domain carrier, and transitive source semantics remain OPEN.
- Proposition 2.3 states positivity throughout the ball at paper lines 486–494. `Draft/Section2.lean:68-75` states positivity away from the pole, while `Defs/Green.lean:70-73` assigns zero at the pole. `FirstPass/S2S3S4S9SA/GreenPole.lean:29-36` supplies a punctured pole limit; an extended-valued source-characterization bridge remains OPEN. The legacy candidate does not establish the literal full source statement.
- At all universes `HarmonicBalls.correctedLemma11_13_forallXi_derived : CorrectedLemma11_13Stmt`, `HarmonicBalls.firstPass_11_11_forallXi_derived : HarmonicBallNotMetricBallStmt`, and `HarmonicBalls.firstPass_1_2_forallXi_derived : HarmonicBallNoveltyStmt` have no outer premises; their file `FirstPass/Phase2/WeylExponentOfDG20.lean:72,76,80` passes the direct warning-as-error check, and each has exactly `[propext, Classical.choice, Quot.sound]` as its printed axiom set. Source correspondence, inner definitions, actual applications and transitive semantic review remain OPEN. The older conditional `hStep8` forms remain conditional; a later declaration does not change their types.
- The corrected 11.13, older `ManyPinchScalesStmt`, and canonical-exponent form have distinct geometry or scope and are not identified by this inventory. Separate canonical candidates are `correctedLemma11_13Canonical_derived`, `harmonicBallNotMetricBallCanonical_derived`, and `harmonicBallNoveltyCanonical_derived` in `FirstPass/Phase2/LocalMetricReplacementDerivedCanonical.lean:24,28,32`; their current elaborated binders, sources, consumers and axioms are NOT YET CHECKED here.
- `step8Identification_derived : Step8IdentificationStmt.{u}` in `FirstPass/Phase2/Step8IdentificationProved.lean` has an exact typed joint-witness application and standard printed axioms. Its independent source, definition, downstream consumer and transitive semantic reviews remain OPEN.

- For 8.2, `firstPass_8_2_S8d_noWeyl_derivedInputsCampbell` has one elaborated outer input: for every probability space, field and circle-average family, `WholePlaneLQGBallMassBounds` holds. The statement of that input is in `Proposed/LQG.lean:172-178`. Its body invokes `firstPass_8_2_S8d_noWeyl_derivedInputs41` with `hSub := dmsLemmaA10WholePlaneMarkedSub_forall` and the retained `hDG`; this exact application was retyped. The candidate source passes a warning-as-error check, and its axiom set and that of the supplied marked identity are each `[propext, Classical.choice, Quot.sound]`. This checks the displayed application and outer binder, not the source correspondence, field normalization, or full transitive semantics. The frozen marked input (`FirstPass/Frozen/S11i.lean:59-67`) includes the subcritical range and measurable nonnegative marked tests; the unmarked Proposed input is distinct. The standalone abstract `MillerSheffieldIG4Prop29` has no other name occurrences in `HarmonicBalls` Lean files; that search does not rule out another implementation of the shift.
- `GreenOccupation.integral_occupation_exitTime_eq_logPotential` (`Proofs/Potential/GreenOccupationCharacterization.lean:225`) proves for bounded open `D`, `y ∈ D`, and smooth compactly supported `g` that Brownian occupation up to exit equals twice the logarithmic-potential difference between the starting point and the expected exit location. Its source passes warning-as-error checking and its axiom set is `[propext, Classical.choice, Quot.sound]`. It is a useful occupation formula, but the displayed statement does not identify `greenFunction` with the occupation density or establish Proposition 2.5's LBM assertion. The general-domain kernel characterization and normalization remain OPEN.

- The six source definitions have corresponding bodies in `Defs/Geometry.lean`; these bodies were printed in Lean, while source equivalence is OPEN. For 10.2, arcs use `circleArc α β` with `α ≤ β < α + 2π`, and simple-arc injectivity is on that arc; the source's arc parameter notation needs separate interpretation. For 10.3, `IsLocallyConnectedSet` quantifies over relative neighborhoods and requires a connected relative neighborhood. For 10.4, `IsCutPoint` requires membership and non-preconnectedness after removal, while compactness, connectedness and local connectedness are carried by applications. For 11.1, the definition uses an arbitrary real linear isometry of the plane; equivalence to the source's coordinate language remains OPEN. For 11.3, `IsCone` allows an open sector or its complement. For 11.4, the boundary-point restriction is carried by applications, not the predicates. Candidate statement uses include `Draft/Section10.lean:108,122` and `Draft/Section11.lean:141,150`; their full elaborated consumer audits remain OPEN.

## Proposed inputs and source references

All eight modules `Proposed/Birkhoff.lean`, `Proposed/DuplantierMillerSheffield.lean`, `Proposed/GilbargTrudinger.lean`, `Proposed/LQG.lean`, `Proposed/LQGDimension.lean`, `Proposed/MetricProperness.lean`, `Proposed/MillerSheffieldIG4.lean`, and `Proposed/PfefferMetricScaling.lean` require full source and semantic review. Frozen bundles and their consumption are OPEN.

Historical candidate edges, requiring exact rechecking: 2.1 refers to `LQGMeasureNonatomic`, `LQGMeasureLocality` and `LQGMeasureWeylScaling` in `Proposed/LQG.lean:86,97,107`; 2.2 refers to `LQGMetricFieldAxioms` in `Proposed/LQG.lean:225`. A faithful 11.16 candidate previously listed `LQGMeasureExistence`, `LQGMeasureWeylScaling`, and `LQGMeasureNonatomic` at `Proposed/LQG.lean:74,107,86` along with frozen and numbered-result inputs; see the Git revision above for its exact candidate and historical receipts. These are leads, not proven producer-to-consumer edges.

For 8.2 the paper uses DMS Lemma A.10 for a marked pair (line 2291) and IG4 Proposition 2.9 for local absolute continuity (2297). The DMS reference in 8.3 is an analogous tail only (2270). Section 11 uses the rooted argument and smooth local drift in 11.7 (3013–3020), IG4 Proposition 2.9 in 11.8 (3002), 11.10 (3179), and 11.9 (3210), and DMS A.10 with a marked extension and Gaussian-shift transfer in corrected 11.13 (3920–3947). The marked whole-plane transfer and the abstract IG4-to-field instantiation are OPEN. See `Proposed/DuplantierMillerSheffield.lean:59,78`, `FirstPass/Frozen/S11i.lean:37,59`, and `Proposed/MillerSheffieldIG4.lean:35-56`.
## Section 11 candidate checks

The following are checked elaborated types of candidate declarations, not assertions that they establish the full numbered source results. Their printed axiom sets are each exactly `[propext, Classical.choice, Quot.sound]`. Source-definition, consumer and transitive semantic checks remain OPEN.

- 11.19: `HarmonicBalls.pinchPointEvent_of_auxiliary_events` takes implicit sets `U V W T Q' Q`, real `δ`, `IsPinchPointProofConfiguration U V W T Q' Q δ`, an implicit real-valued `D`, `IsEuclideanLengthMetric D`, `∀ x y, 0 ≤ D x y`, a measure `μ`, real `M`, and the three predicates `pinchFirstEvent D W T Q' Q δ`, `pinchSecondEvent μ D U V δ M`, `pinchThirdEvent D V W δ`; it concludes `pinchPointEvent μ D U T Q' Q M 1 0`. Equivalence of the predicates and configuration to the exact corrected source is OPEN.
- 11.23: `HarmonicBalls.coordinateSigmaMixing_canonical` takes an implicit measurable sample space, measure `P`, field pairings `hC`, circle averages `hcirc`, an `IsProbabilityMeasure P` instance, and `IsWholePlaneGFF P hC hcirc`; its conclusion is `coordinateSigmaMixing (canonicalLaw hC P) (fun i L => L i) dilOp`. `HarmonicBalls.ergodic_dilOp` takes the same binders and concludes `Ergodic dilOp (canonicalLaw hC P)`. The treatment of the field modulo constants and the fixed logarithmic drift in the corrected source remains OPEN.
- 11.24: `HarmonicBalls.pinchPointEvent_keyhole_subset_metricBall` and `HarmonicBalls.pinchPointEvent_outer_subset_compl_metricBall` each take `μ D U T Q' Q M r u w z`, `IsPinchPointConfiguration U T Q' Q`, `IsEuclideanLengthMetric D`, nonnegativity of `D`, `pinchPointEvent μ D U T Q' Q M r z`, `0 < r`, `w ∉ Metric.ball z (10 * r)`, and `z ∈ frontier (lqgMetricBall D w u)`. They conclude respectively that `rescaledSet T r z` is inside the metric ball and `rescaledSet Q' r z` is in its complement. The latter conclusion alone yields a non-strict lower distance bound, whereas the paper states a strict bound. The event also includes a mass clause, so matching the source's two metric inequalities requires a separate check.

For 11.24, the two full candidate applications above have also been retyped together at the argument types used in `Proofs/Sec11/PinchAnnulus.lean:23-26`. The same two declarations are used in `Proofs/Sec11/PinchMetricBall.lean:41-44`; the printed axiom sets of `pinchPointEvent_not_annulusMassBound` and `pinchEventMetricBallConsequence_of_metricFieldAxioms` are each `[propext, Classical.choice, Quot.sound]`. This checks the indicated applications, not the full exact-source composition or the source's strict outer inequality.
