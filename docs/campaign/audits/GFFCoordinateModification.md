# GFF coordinate modifications and representation

`HarmonicBalls.Defs.GFF.IsWholePlaneGFF` (Defs/GFF.lean:93) requires
measurable deterministic test pairings, Gaussian finite-dimensional laws,
the prescribed means and covariances, and a continuous circle-average
modification. It does not require one event on which all pairings are linear.

`IsWholePlaneGFF.coordinateModification` proves that all six fields survive a
measurable replacement equal almost surely at each deterministic test.
`IsWholePlaneGFF.comp_measurePreserving` proves the complete GFF interface
pulls back along a measure-preserving map, including the mixed observables.

`IsWholePlaneGFF.product_has_ae_non_linear_modification` gives a checked relative
counterexample: from **any** project-interface GFF, it constructs a GFF on its
product with a standard real Gaussian probability space, with identical circle
averages and pairings that agree at every fixed test almost surely, such that
at almost every sample there is a test witnessing failure of scalar linearity.
The counterexample retains all six GFF fields. It requires existence of a
starting `IsWholePlaneGFF`; the code does not establish that existence.
Consequently it rules out proving a common samplewise representation from the
GFF predicate alone whenever that predicate is inhabited, but does not itself
produce an unconditional inhabitant.

The proof takes a smooth compactly supported nonzero bump φ₀ and the injective
curve `a r = r • φ₀`. A diagonal spike changes a pairing only at `a t`, where
t is the independent Gaussian coordinate. Every fixed test changes on at most
one null t-fiber. The spike size is chosen as 1 or 2 using the original values at `a t` and
`a (2t)`, so the scalar relation between them fails whenever t is nonzero,
regardless of whether the starting pairings were linear. At a fixed test, the
spike is measurable: on its unique possible t-fiber the two original tests
are deterministic. `IsWholePlaneGFF.exists_ae_non_linear_modification`
formalizes this argument, including section measurability. The conclusion is
`∀ᵐ ω, ∃ test, ...`; it is stronger than the negation of a common linearity
event and does not require the displayed existential event to be measurable.

The precise invalid exchange is from `∀ φ, ∀ᵐ ω, ...` to `∀ᵐ ω, ∀ φ, ...`.
`IsWholePlaneGFF.exists_meanZero_distribution_version`
(MeanZeroDistributionVersion.lean:47) supplies equality almost everywhere
separately for each mean-zero test, not on a common event.

Leonardo Bonanno's `GFFExist.exists_normalizedWPGFF` (ExistGFF.lean:85)
constructs a distribution-valued field with his normalized GFF predicate;
`CircleAvgKolm.exists_continuous_version_circleAvg` (CircleAvgKolm.lean:175)
constructs a continuous circle-average version, and
`CircleAvg.exists_isGFFCircleAverage_normalized` (CircleAvgBridge.lean:129)
establishes its circle-only Gaussian law and covariance.
`normalizedGFF_allPairings_gaussian` proves that Bonanno's normalized field
has centered jointly Gaussian pairings for all tests, using
`MarkovNorm.pairVec_mem_gaussSpace` (MarkovNorm.lean:98).
`normalizedGFF_pairing_covariance_tendsto` identifies the covariance of any
two pairings as the limit of Bonanno's logarithmic covariances of their
mean-zero approximations, using the `L²` convergence of those approximations.
`abs_logPot_meanZeroApprox_sub_le` bounds the difference between the
approximation’s logarithmic potential and the normalized potential uniformly
by `|∫ φ| · 2⁻ⁿ`. Theorems
`tendsto_integral_test_mul_meanZeroApprox_error` and
`tendsto_integral_meanZeroApprox_mul_error` show that this error vanishes
after integration against a fixed test or another mean-zero approximation;
the latter uses uniform boundedness of their absolute masses. Identifying the
remaining limiting integral with the project kernel is still required.
`normalizedGFF_pairings_increments_gaussian` also proves the mixed Gaussian
law of all pairings and positive-radius circle-average increments. It uses
the almost-sure limit of mollified increments, which are mean-zero test
pairings, and preserves their joint Gaussian law with all test pairings.
`normalizedGFF_exists_joint_circle_version` constructs a jointly continuous
circle-average version that is jointly Gaussian with all test pairings and
agrees with Bonanno's circle averages almost surely at every fixed circle;
it also has the project-prescribed circle-circle covariance.
`wholePlaneCov_eq_additive_of_ne` identifies the project kernel with the
additive logarithmic kernel away from the diagonal, and
`wholePlaneGFFCov_circle_eq_gffCircleCov` removes the diagonal discrepancy
under circle smearing using its codiscreteness.
`Section6.map_pairingProc_eq`
(AnnulusLawTransfer.lean:96) transfers only mean-zero pairing laws starting
from an existing project GFF. A direct existence bridge to all six fields of
this repository's GFF interface, including test-test and mixed test-circle
covariances, has not been established here.
No numbered-result closure follows.
