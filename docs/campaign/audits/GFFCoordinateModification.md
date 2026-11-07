# GFF coordinate modifications and representation

`HarmonicBalls.Defs.GFF.IsWholePlaneGFF` (Defs/GFF.lean:93) requires
measurable deterministic test pairings, Gaussian finite-dimensional laws,
the prescribed means and covariances, and a continuous circle-average
modification. It does not require one event on which all pairings are linear.

`IsWholePlaneGFF.coordinateModification` proves that all six fields survive a
measurable replacement equal almost surely at each deterministic test.
`IsWholePlaneGFF.comp_measurePreserving` proves the complete GFF interface
pulls back along a measure-preserving map, including the mixed observables.

`IsWholePlaneGFF.product_has_non_linear_modification` gives a checked relative
counterexample: from **any** project-interface GFF, it constructs a GFF on its
product with a standard real Gaussian probability space, with identical circle
averages and pairings that agree at every fixed test almost surely, such that
there is no almost-sure event of scalar linearity simultaneously at every test.
The counterexample retains all six GFF fields. It requires existence of a
starting `IsWholePlaneGFF`; the code does not establish that existence.
Consequently it rules out proving a common samplewise representation from the
GFF predicate alone whenever that predicate is inhabited, but does not itself
produce an unconditional inhabitant.

The proof takes a smooth compactly supported nonzero bump φ₀ and the injective
curve `a r = r • φ₀`. A diagonal spike changes a pairing only at `a t`, where
t is the independent Gaussian coordinate. Every fixed test changes on at most
one null t-fiber. If the starting GFF has a common linearity event, the spike
breaks the relation between `a t` and `a (2t)` almost surely; otherwise the
starting GFF itself already provides the desired failure. Thus no samplewise
linearity hypothesis is needed. `diagonalSpike_sections` checks measurability
of each section; `IsWholePlaneGFF.exists_modification_not_ae_linear` checks
the case split. The conclusion is the negation of `∀ᵐ ω, ∀ test ...`; it does
not assert that the event of nonlinearity is measurable or has probability one.

The precise invalid exchange is from `∀ φ, ∀ᵐ ω, ...` to `∀ᵐ ω, ∀ φ, ...`.
`IsWholePlaneGFF.exists_meanZero_distribution_version`
(MeanZeroDistributionVersion.lean:47) supplies equality almost everywhere
separately for each mean-zero test, not on a common event.

Leonardo Bonanno's `GFFExist.exists_normalizedWPGFF` (ExistGFF.lean:85)
constructs a distribution-valued field with his normalized GFF predicate;
`CircleAvgKolm.exists_continuous_version_circleAvg` (CircleAvgKolm.lean:175)
constructs a continuous circle-average version. `Section6.map_pairingProc_eq`
(AnnulusLawTransfer.lean:96) transfers only mean-zero pairing laws starting
from an existing project GFF. A direct existence bridge to all six fields of
this repository's GFF interface, including arbitrary test and mixed circle
covariances, has not been established here. No numbered-result closure follows.
