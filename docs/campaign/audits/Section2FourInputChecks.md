# Section 2 four-input consumption check

`HarmonicBalls/Audit/Section2FourInputChecks.lean` applies both exports from
`Proofs/Sec2/SingularAtomAtZero.lean` to the expanded frozen I2 and I1 types in
`Draft/Section2.lean:109,122`, at arbitrary universe `u`. The I2 event precedes
all radii and admissible exponents; its radius threshold can depend on them.
I1 has one event for all nonempty open subsets of the plane. These are
conditional checks, not unconditional closure of either input.
This supplements `Section2VolumeGrowthInputs.md`, whose earlier six-input
producer takes Weyl scaling and singular nonatomicity as hypotheses; the
four-input producer checked here derives both instead.

The four universally quantified hypotheses are exactly:

1. `WholePlaneLQGBallMassBounds`: the Ding–Gwynne Lemma 3.8 whole-plane,
   zero-insertion mass estimate, for every admissible measure and exponent
   pair, with polynomially high probability uniformly over the unit square.
2. `WholePlaneGFFAffineInvariance`: each deterministic nonzero complex affine
   map yields the normalized whole-plane GFF law; no simultaneous samplewise
   law over maps is asserted.
3. `LQGMeasureCoordChange` only at insertion zero: for each eligible random
   measure, one almost-sure event works for all nonzero affine scales and
   translations. The mapped measure uses the inverse affine map.
4. `LQGMeasureExistence` for every insertion parameter, with subcriticality
   inside the Prop: on the same probability space there is a locally finite
   dyadic vague limit almost surely. It is not merely existence at zero.

The Proposed interfaces remain subject to operator source review. The source
audit at `SOURCE-AUDIT-20261107.md:55-146` distinguishes the direct HB §2.2
background existence assertion for the singular whole-plane field from DS
Proposition 1.1 and BP Theorem 2.1, which treat bounded-domain Dirichlet fields;
transfer at the pole needs additional work. HB Fact 2.1 IV supplies the direct
background coordinate-change scope: DS Proposition 2.1 handles a fixed map,
while the cited Sheffield–Wang simultaneity result starts in a bounded-domain
setting. The dyadic definition alone does not supply convergence at shifted
scales. The affine law is separately quantified for each deterministic map.
These remarks do not admit new sources or assert that original theorems alone
give the full interfaces.

`singular_nonatomic_of_existence_and_wholePlane` derives the singular
nonatomicity interface, which is checked independently in the Lean file.
`Section6.lqgMeasureNonatomic_of_existence` chooses `β = (α + Q)/2`, so
`α < β < Q`, and obtains the stronger measure from the same field. At zero,
`origin_nonatomic_of_stronger_singularity` compares the weaker measure with
arbitrarily small constant multiples of the locally finite stronger measure;
the resulting bound tends to zero. Away from zero, a punctured-plane weighted
identity and the zero-insertion mass estimate give absolute continuity with
respect to a nonatomic measure. This is not an inference that vague limits of
nonatomic measures are nonatomic. Weyl scaling is proved from the limit
definition. The I2 producer consumes the derived nonatomicity and the three
whole-plane inputs; I1 then follows from the proved I2 lower bound. There is
no metric hypothesis and no use of I2 to obtain the nonatomicity needed for
I2. The Lean type checks do not verify the cited source claims.
