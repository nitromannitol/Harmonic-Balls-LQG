# Phase 2 catalog: what the pinned stack already proves

Read-only survey (task fp-phase2-lp-catalog, worker z3, 2026-11-10). No Lean file was edited and nothing was built.
Method: grep of declaration heads and line ranges; statements read only for the lines shown.

## Pins and tags

| Tag | Repository (path under the HB `.lake/packages/` unless stated) | Commit |
|---|---|---|
| [LP] | Lattice-Probability, `/home/nitro/lean/Lattice-Probability-v435`, branch lean-v4.35, paths under `LatticeProb/` | 3912597 (= HB pin) |
| [ER] | `elliptic_regularity/` (paths relative to it) | 1e29da0 |
| [MP] | `MarkovProcess/` (paths relative to it, e.g. `MarkovProcess/Main.lean`) | 666cda0 |
| [ML] | `mathlib/Mathlib/` | 06535612 |

- "found" = a declaration whose head was read and which carries a proof (or is a definition/structure as marked).
- Conditional entries take a named hypothesis (structure, residual Prop, or `IsGFFCircleAverage`); they are marked (cond).
- Sorry check: no `sorry` or `admit` token in any cited file. The word `sorry` occurs only in comments of
  `Prob/GaussianLogSobolevOne.lean:14,132`, `Prob/AkcogluKrengelAE/RectangleErgodic.lean:38` and a few other files.
  `#print axioms` was NOT run for any entry; this is a grep result only.

## 1. Gaussian free field: whole-plane, zero-boundary, circle averages, Markov property, Cameron-Martin

Found (10):
1. `IsWholePlaneGFF` (structure, DistC-valued h under P; first field measurability): [LP] `Bonanno/LQGMetric/Statement/GFF.lean:41`.
2. `IsZeroBoundaryGFF` (structure on open U): [LP] `Bonanno/LQGMetric/Field/ZeroBoundary.lean:61`; `IsZBGFFProcess` at :53.
3. `gff`, `covariance_gff`: [LP] `Network/GFF.lean:158,173`. Discrete GFF killed on C; covariance = killed Green matrix (connected G, q ∉ C).
4. `ae_circleAvg_addConst_of_logCov_le`: [LP] `Bonanno/LQGMetric/Field/CircleAvgLimit.lean:115`. A.s. limit of circle averages of a whole-plane GFF up to an additive constant, under a log-covariance bound (0<q<1). `ae_tendsto_mollAvg_of_logCov_le` at :102.
5. `isGaussianProcess_mollAvg_sub`, `hasGaussianLaw_mollAvg_sub`, `covariance_mollAvg_sub`: [LP] `Bonanno/LQGMetric/Field/CircleAvgGauss.lean:61,71,82`. Mollified circle averages are Gaussian with explicit covariance.
6. `tiltMeasure`, `isProbabilityMeasure_tiltMeasure`, `integral_tiltMeasure`: [LP] `Prob/CameronMartin.lean:62,163,183`. Cameron-Martin tilt by exp of a finite linear combination (finite-dimensional, not the GFF as such).
7. `cmDensity`, `measurable_cmDensity`: [LP] `Bonanno/LQGMetric/Field/CameronMartin.lean:64,66`; `cmLin` (zero-boundary Cameron-Martin map to L²(P)): `Bonanno/LQGMetric/Field/MarkovZB.lean:101`.
8. `lmLem2_1`: [LP] `Bonanno/LQGMetric/Field/MarkovFinal.lean:46`. Markov property of the whole-plane GFF, stated as `Blueprint.LMLem2_1` (that Prop not read here). Support: `MarkovVer2Fub.lean:133,139`.
9. `zsSub` (zero-boundary Cameron-Martin test space as a submodule): [LP] `Bonanno/LQGMetric/Field/MarkovZB.lean:62`.
10. `exists_dist_version_zbExt` (zero-boundary extension of a version of the distance; cond on `IsNormalizedWPGFF`): [LP] `Bonanno/LQGMetric/Field/MarkovVer2Fub.lean:283`.

Absent or not located:
- Girsanov theorem for `IsWholePlaneGFF` beyond the finite Cameron-Martin tilt (only `Prob/CameronMartin.lean` exists).
- An unconditional construction theorem for the whole-plane GFF as a measure. `Bonanno/LQGMetric/Field/Exist*.lean` exist (`ExistKernelL2`, `ExistSFub2`, `ExistKerId`); their main statements were NOT read (partial grep).

## 2. LQG measure (Gaussian multiplicative chaos)

Found (10):
1. `ae_measure_singleton_eq_zero`: [LP] `Bonanno/MatedCRTHarmonic/GMCFacts/NoAtom.lean:49`. Non-atomicity of the GMC measure μ (cond: `LQGDimension.IsGFFCircleAverage H P`, measurable circle averages, γ).
2. `lintegral_dens_le_one`: `GMCFacts/NoAtom.lean:32` (helper for 1).
3. `isLocallyFiniteMeasure_lqgApprox`: [LP] `Bonanno/MatedCRTHarmonic/GMCFacts/LowerTail.lean:59` (cond: `IsGFFCircleAverage`). Approximating measures `GMSLemma27.lqgApprox γ H k ω` are locally finite.
4. `gmcLowerTail_holds`: [LP] `GMCFacts/LowerTail.lean:258`. For 0<γ<2, proves `GMSLemma27.GMCLowerTail γ` (Prop defined at `Bonanno/MatedCRTHarmonic/GMSLemma27/GMCInterfaces.lean:69`).
5. `measure_ball_small_le`, `measure_sq_small_le`: [LP] `GMCFacts/LowerTail.lean:180,114`. Small-ball and small-square mass bounds (cond on `IsGFFCircleAverage`).
6. `exists_measurable_version`: [LP] `Bonanno/MatedCRTHarmonic/GMCFacts/Version.lean:89` (cond). Measurable version of the circle-average family. A different, generic lemma with the same name: `Bonanno/QuantumZipper/Proofs/GFF/CircleFubini.lean:431`.
7. `exists_uniform_neg_moment_nM`: [LP] `Bonanno/LQGMetric/Dimension/GMCMomentNeg3Cmp.lean:168` (zero-boundary GFF on `openSquare`, 0<γ<2, p<0). Uniform negative moment of the GMC mass. Also `integral_nM_rpow_le` at :33.
8. `LogCorr.exists_uniform_moment`: [LP] `Bonanno/LQGMetric/Dimension/GMCMomentPos2Main.lean:227` (1<q<4/β). Uniform positive moment for log-correlated fields; `LogCorr.recursion` at :95.
9. `gmcConst_lt_top`: [LP] `Bonanno/LQGMetric/Dimension/GMCMass.lean:58`. Finiteness of the constant `gmcConst γ` (def `GMCMoment.lean:42`).
10. `LQGDimension.IsGFFCircleAverage` (structure, the hypothesis of most GMC facts): [LP] `Bonanno/LQGDimension/Statement/Defs.lean:106`.

Absent or not located:
- A named LQG measure object (`IsLQGMeasureOfField`) in LP. It exists only in HB (`HarmonicBalls/...`).
- Coordinate-change identity (z ↦ affine map) or Weyl scaling for the GMC measure: no declaration found. The word "Weyl" appears only in metric files (§3).
- Non-atomicity for a general GMC measure: only in the `IsGFFCircleAverage` setting (item 1).

## 3. LQG metric: axioms, Weyl scaling, locality, existence

Found (10):
1. `IsStrongLQGMetric` (structure, D : DistC → ContMetric): [LP] `Bonanno/LQGMetric/Statement/LQGMetric.lean:38`. Fields include `measurable`, `length` (a.s. length space), `locality` (for open U the internal distance is a.s. determined by h|U). Further fields not read.
2. `IsWeakLQGMetric` (structure, with additive function c): `LQGMetric.lean:82`.
3. `IsStrongLQGMetric.ae_dist_addConst`: [LP] `Bonanno/LQGMetric/Metric/WeylLQG.lean:72`. A.s., for all constants c and z, w: a distance identity under the additive shift h ↦ h + c (exact formula at :72-79, not transcribed).
4. `IsWeakLQGMetric.ae_dist_addConst`: `WeylLQG.lean:80`.
5. `IsStrongLQGMetric.ae_internal_addFun_of_eq_const`: `WeylLQG.lean:89`; weak version `:99`. Internal distance under an addition constant on U.
6. `weylScale` (def): [LP] `Bonanno/LQGMetric/Statement/Metric.lean:96`. `ContMetric`, `IsContinuousMetric`, `IsMetricFn` at `Statement/Metric.lean:50,46,38`.
7. `weylScaleOn_eq_internal`: [LP] `Bonanno/LQGMetric/Metric/WeylLength.lean:240`; `internal_eq_of_eq_const` at :246.
8. `isLength_of_eq_weylScale`: `WeylLength.lean:261`.
9. `IsStrongLQGMetric.translation`: [LP] `Bonanno/LQGMetric/Papers/GM/S1/StrongWeak.lean:133`.
10. `gm_s1_7` (weak to strong, Gwynne-Miller S1 lemma 7 by name): [LP] `StrongWeak.lean:85`. Statement not read.

Absent or not located:
- Existence of an LQG metric as an unconditional theorem: no declaration found. `ExistsNormalizedGFF` (Prop def, `Papers/GM/S1/Defs.lean:91`) and `exists_MQSpec` (`Papers/GM/S2/SpatialIndepAsm5.lean:47`, takes `MQLem4_1Gen`) are conditional.
- Locality as a separate theorem: it is a field of `IsStrongLQGMetric`, not a lemma.

## 4. Gaussian measures and processes

Found (10):
1. `IsGaussian` (class; characteristic-functional characterization `IsGaussian.charFun_eq`): [ML] `Probability/Distributions/Gaussian/Basic.lean`.
2. `gaussianReal` (def, one-dimensional Gaussian law): [ML] `Probability/Distributions/Gaussian/Real.lean`.
3. `IsGaussian.integrable_dual`, `IsGaussian.memLp_dual`: [ML] `Gaussian/Basic.lean`.
4. `isoProc`, `memLp_isoProc`, `integral_isoProc`: [LP] `Gauss/Process.lean:26,37,45`. Isonormal process from a Hilbert basis.
5. `LatticeProb.gaussianProcess_map_eq_of_covariance`: [LP] `Prob/GaussianLaw.lean:97`. Law of a Gaussian process determined by its covariance.
6. `borellTIS_gaussianVector`: [LP] `Prob/GaussBorellVector.lean:77`. Borell-TIS sup inequality for a centred Gaussian vector.
7. `borellTIS_iSup_seq`: [LP] `Prob/GaussBorellSeq.lean:93`. Borell-TIS for a countable sup of an `IsGaussianProcess`.
8. `tail_iSup_le`: [LP] `Prob/GaussSupTailField.lean:111`. Tail bound for the sup of a centred Gaussian process.
9. `measure_ge_le_of_mgf_bound`: [LP] `Prob/GaussianConcentration.lean:45`. Tail bound from an MGF bound. `integrable_exp_lipschitz_gaussian` at :79.
10. `gaussianLogSobolevGrad_one_of_residual`: [LP] `Prob/GaussianLogSobolevAssembly.lean:58` (cond on `GaussianLogSobolevResidual`, def :53). Log-Sobolev is conditional on the residual Prop.

Absent or not located:
- The predicate `IsGaussianProcess` is used throughout LP (e.g. `Prob/GaussBorellSeq.lean:39`, `Prob/GaussSupTailField.lean:78`), but its defining declaration was not found by name in LP, the Mathlib pin or the packages (grep of `def|structure|class|abbrev` forms). OPEN: the lead should locate it or confirm it is defined under another keyword.
- Borell-TIS or Gaussian concentration in Mathlib: not checked.

## 5. Green functions and harmonic measure

Found (10):
1. `greenExists` (d ≥ 3, divergence-form coefficients): [ER] `Ch4Statements/GreenExists.lean:16`. Proof delegated (`exact PDE.GreenExistsProof.result`) to [ER] `EllipticRegularity/Ch4/GreenExistsProof.lean`.
2. `greenMaxPrinciple` (d ≥ 2): [ER] `Ch4Statements/GreenMaxPrinciple.lean:13`. Statement file delegates by `exact`; proof module not read.
3. `greenDecay` (d ≥ 2, R ≥ 10): [ER] `Ch4Statements/GreenDecay.lean:14`; `greenDirichlet` (d ≥ 2): `Ch4Statements/GreenDirichlet.lean:14`. Same status as 2.
4. `killedGreenReal`, `killedGreenReal_nonneg`: [LP] `Network/KilledGreen.lean:55`; `killedGreen_vanishes` at :88 (zero at v ∉ C); `sum_tsum_killedHeat` at :61.
5. `killedGreenMatrix`, `killedGreenMatrix_posSemidef`: [LP] `Network/GFF.lean:26,58` (connected graph, killed Green matrix is PSD).
6. `srwGreenInf` (def, ∑_j srwHeat): [LP] `Walk/SimpleTransfer.lean:25`; `walkOp_srwGreenInf` (d ≥ 3): `Walk/ExteriorDirichlet.lean:114`; `tendsto_srwGreenInf_zero` (d ≥ 3): `ExteriorDirichlet.lean:163`.
7. `le_mul_of_nonneg_harmonicOn` (discrete Harnack-type constant, scale R ≥ 4): [LP] `Walk/Harnack/GreenEstimates.lean:460`. Conclusion beyond ∃ C not read.
8. `le_of_harmonic_on_box`: [LP] `Walk/ExteriorDirichlet.lean:60`.
9. `integral_openExit_harmonic_compactSupport`: [LP] `Prob/BrownianOpenHarmonicExit.lean:53` (d ≥ 1). Exit-position integral of a harmonic function (by name; the exact identity was not read; verify before use). Also `:89`, `:125`, `:133`.
10. `IsHarmonicOn`, `IsHarmonicOn.laplacian_eq_zero`: [LP] `Analysis/HarmonicBridge.lean:31,39`.

Absent or not located:
- "Harmonic measure" by name: not found. The exit law of a Brownian path from U is present in [MP] `Trajectory/ExitLaw.lean` (`measurableSet_exitTime_lt_top` :53, `measurable_eval_untopD_exitTimeTop` :66); its identification with harmonic measure is not checked.
- Continuous Green function on a domain as an object for the general elliptic PDE: only the d ≥ 2, 3 statements in [ER] (§5 items 1-3).

## 6. Potential theory: harmonic and subharmonic functions, maximum principle, Harnack, obstacle and balayage

Found (10):
1. `InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant` (Liouville, vector valued): [ML] `Analysis/Complex/Harmonic/Liouville.lean:48`.
2. `HarmonicOnNhd.circleAverage_eq` (mean value property): [ML] `Analysis/Complex/Harmonic/MeanValue.lean:67`. Also `HarmonicContOnCl.circleAverage_eq` at :95.
3. `HarmonicAt.analyticAt` (harmonic in ℂ implies real-analytic): [ML] `Analysis/Complex/Harmonic/Analytic.lean:143`.
4. Poisson kernel: `HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul`: [ML] `Analysis/Complex/Harmonic/Poisson.lean:42`.
5. `subharmonic_maximum_principle` (discrete, boundary-accessible A): [LP] `Network/Dirichlet.lean:82`. `boundaryAccessible_of_strict_subharmonic` at :291.
6. `harmonic_mono`, `harmonic_add`, `maximum_neighbors`: [LP] `Network/HarmonicAlgebra.lean:29,36,66`.
7. `harnack_constant_ge_one` (d ≥ 2): [ER] `Ch4Statements/HarnackConstantGeOne.lean:14`. Statement file delegates by `exact`.
8. `exists_harnack_constant` (De Giorgi-Nash-Moser Harnack constant, d ≥ 3): [ER] `DGNMStatements/Harnack.lean:12`. Proof: [ER] `EllipticRegularity/DeGiorgi/Assembly/Harnack.lean` (file exists; proof not read).
9. `le_mul_of_nonneg_harmonicOn` (discrete Harnack): [LP] `Walk/Harnack/GreenEstimates.lean:460` (see §5.7).
10. `IsHarmonicOn` / `isHarmonicOn_iff_harmonicOnNhd`: [LP] `Analysis/HarmonicBridge.lean:31,57`.

Absent or not located:
- Obstacle problem and general balayage: no declaration. The only balayage in LP is the half-disc balayage `bal μ = μ.bind P` at `Bonanno/QuantumZipper/Proofs/GFF/K3/HalfDiscMarkov.lean:13,302-371`, which is not the obstacle problem.
- Continuous subharmonic maximum principle in ℂ or ℝ^d: not found in Mathlib or LP (only the discrete one, item 5).

## 7. Brownian motion and stopping times

Found (10):
1. `brownianMotion_map_prodMk_shift`: [MP] `MarkovProcess/Examples/BrownianMotion.lean:81`. Joint law of (B_s, shifted path) for Brownian motion from x.
2. `IsFellerKernelSemigroup.continuousProcess_condExp_shift_stoppingTime`: [MP] `MarkovProcess/Main.lean:286`. Strong-Markov type identity at a stopping time (`..._countableStoppingTime` at :302).
3. `isStoppingTime_exitTime` (continuous paths): [MP] `MarkovProcess/Path/ExitTime.lean:260`.
4. `killAtExit` (lifetime = exitTime U ω): [MP] `MarkovProcess/Killed/KillAtExit.lean:58`; `coordinate_killAtExit` at :92.
5. `IsConservative.killedKernelOn`, `killedSemigroup`: [MP] `MarkovProcess/Killed/Semigroup.lean:61,159`.
6. `IsBrownianSpace.hasStrongMarkovRestart`: [LP] `Prob/BrownianStrongMarkov.lean:302`. Brownian motion in ℝ^d has the strong Markov restart (structure `HasStrongMarkovRestart`: `Prob/BrownianMarkov.lean:183`; `.law` at :199).
7. `isStoppingTime_exitTime` (Brownian, measurable paths): [LP] `Prob/BrownianExitTime.lean:93`.
8. `openExitTime_mem_frontier`: [LP] `Prob/BrownianOpenExit.lean:72`. Exit position lies on the frontier.
9. `measure_abs_ge_le_exp`: [LP] `Prob/BrownianMax.lean:69`. Exponential tail bound for a pre-Brownian real process (conclusion not read in full).
10. `exitTime_le_iff`, `measurableSet_comap_exists_le_le_norm`: [LP] `Prob/BrownianExitTime.lean:39,62`. Also `openExitTime_not_mem` at `Prob/BrownianOpenExit.lean:50`; `Prob/BrownianOpenExitStopping.lean` and `BrownianFiniteStopping.lean` exist (names not read).

Absent or not located: none found for these categories beyond the above (Mathlib stopping times were not re-checked).

## 8. Random walk

Found (10):
1. `exists_binomPMF_localCLT`: [LP] `Walk/BinomialLocalCLT.lean:1481`. Local CLT for the binomial pmf with a uniform constant (parity constraint on j).
2. `exists_binomLaw_localCLT`: [LP] `Walk/BinomLaw.lean:569` (primed variant `:610`).
3. `nbrSum_eq_sum_dir`, `walkOp_eq_sum_dir`: [LP] `Walk/Basic.lean:64,71`. SRW generator as the sum over 2d directions.
4. `tsum_harmonic_eq_top`: [LP] `Walk/PolyaRecurrence.lean:372`. ∑ 1/(4(m+1)) = ∞ in ℝ≥0∞ (recurrence input).
5. `harmonic_le_srwKernel`: [LP] `Walk/PolyaRecurrence.lean:410` (hypothesis: centralBinom count identity).
6. `exit_time_bounds` (d ≥ 1): [LP] `Walk/ExitTime.lean:217`. Conclusion not read.
7. `tendsto_srwGreenInf_zero`, `walkOp_srwGreenInf` (d ≥ 3): [LP] `Walk/ExteriorDirichlet.lean:163,114` (see §5.6).
8. `le_of_harmonic_on_box`: [LP] `Walk/ExteriorDirichlet.lean:60`.
9. Pointers, names not read: [LP] `Prob/Scaling/WalkCLT.lean`, `Walk/ContinuousHeatGauss.lean`, `External/BallGreenBoundsProved.lean`, `External/GreenNormsProved.lean`.
10. [LP] README lists "simple random walk on ℤ^d and on locally finite graphs" as proved (README.md:11-20).

Absent or not located: Donsker invariance for SRW to Brownian motion as a single named theorem (`Prob/Scaling/WalkCLT.lean` and `BrownianFdd.lean` are the candidates; not checked).

## 9. Ergodic theorems (Birkhoff)

Found (10):
1. `ae_tendsto_bAvg`: [LP] `Prob/Birkhoff.lean:671`. A.e. convergence of Birkhoff averages for measure-preserving T on a finite μ and integrable f.
2. `maximal_inequality`: [LP] `Prob/Birkhoff.lean:59`. Birkhoff maximal inequality (c > 0).
3. `ae_cauchySeq_bAvg`, `ae_tendsto_bLimsup`, `ae_bLiminf_eq_bLimsup_of_bounded`: [LP] `Prob/Birkhoff.lean:660,679,430`.
4. `maxBirkhoff` (def) and `maxBirkhoff_mono`: [LP] `Prob/MaximalErgodic.lean:29,50`.
5. `LatticeProb.measurable_bLimsup_invariants`: [LP] `Prob/ErgodicDecomposition.lean:22`. `bLimsup_ae_eq_condExp_of_bounded` at :85.
6. `KernelStationary`, `KernelInvariant` (defs): [LP] `Prob/KernelErgodicDecomposition.lean:48,54`.
7. `Ergodic` (structure, f and μ): [ML] `Dynamics/Ergodic/Ergodic.lean:49`. Mathlib notion; `ae_empty_or_univ` at :61.
8. Mathlib Birkhoff sums: `birkhoffSum_ae_eq_of_ae_eq`, `birkhoffAverage_ae_eq_of_ae_eq`: [ML] `Dynamics/BirkhoffSum/QuasiMeasurePreserving.lean:35,43`.
9. Akcoglu-Krengel for boxes: `Prob/AkcogluKrengelAE/BirkhoffLpMaximalProved.lean` (sorry-free, file header says only the three standard axioms). Names inside not read.
10. [LP] README: "ergodic theorems and zero-one laws" listed as proved (README.md:11-20).

Gaps (not proved, do not cite as proved):
- `Prob/AkcogluKrengelAE/RectangleErgodic.lean:38`: "Two steps are still missing."
- `Prob/AkcogluKrengelAE/BallMaximalLp.lean:34`: two Props "mark the exact remaining gap" (conditional).

Absent or not located: a Mathlib a.e. Birkhoff convergence theorem by name (checked names with `ae_tendsto` in `Dynamics/BirkhoffSum` and `Dynamics/Ergodic`: none).

## 10. Measurability: kernels and measurable selection

Found (6):
1. `exists_measurable_selection`: [LP] `Prob/Scaling/MeasurableLocalChoice.lean:14`. Measurable selection for countably many measurable predicates p n and measurable f n. Conclusion not read in full.
2. `condCopyKernel` (def) and `CopyMeasure`, `CopyMeasure_fst`, `CopyMeasure_apply_prod`: [LP] `Prob/CondCopies.lean:53,67,79,85`. Conditional copies of Y given X on a finite measure.
3. `LatticeProb.measurable_integral_condExpKernel_param`: [LP] `Prob/CondExpParamMeas.lean:8`. Measurability in a parameter for a conditional-expectation kernel (StandardBorel target).
4. `Eventually.exists_measurable_mem`: [ML] `MeasureTheory/MeasurableSpace/MeasurablyGenerated.lean:95`.
5. `Eventually.exists_measurable_mem_of_smallSet`: [ML] same file, :99.
6. `RandomShiftMeasurability`: [MP] `MarkovProcess/Path/RandomShiftMeasurability.lean:52,61,68` (`measurable_of_isStoppingTime`, `measurable_shift_stoppingTime`).

Absent or not located:
- Kuratowski-Ryll-Nardzewski or Jankov-von Neumann type selection theorems (for closed or analytic sets) in Mathlib or LP: no declaration found. LP `exists_measurable_selection` covers countable families only.

## Open questions and notes for the lead

1. `IsGaussianProcess`: used by many LP lemmas; its defining declaration is not located (see §4).
2. Proof modules of `greenMaxPrinciple`, `greenDecay`, `greenDirichlet`, `harnack_constant_ge_one` in [ER] were not checked (statement files delegate by `exact`).
3. `#print axioms` not run; no sorry token found in cited files (comments only).
4. Conditional or gapped entries: `GaussianLogSobolevAssembly.lean:58` (residual), `RectangleErgodic.lean:38`, `BallMaximalLp.lean:34`.
5. LQG content in LP is in `Bonanno/*` (LQGMetric, LQGDimension, MatedCRTHarmonic, QuantumZipper). Most GMC and metric facts take named hypotheses; the catalog lists names, not unconditional status.
6. Heartbeat and naming: the lead should not rely on the `exists_measurable_version` name for GMC; two different declarations share it (§2.6).
