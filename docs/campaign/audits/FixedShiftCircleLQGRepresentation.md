# Fixed smooth shifts: circle and normalized-mass representation

`HarmonicBalls.Proofs.GFF.FixedShiftCircleLQGRepresentation` records partial
infrastructure for Lemma 11.8; it does not close the representation gap.
The results use the actual whole-plane GFF joint Gaussian/covariance axioms
and the annular tests of `LocalCirclePairingApproximation`, not a postulated
joint circle/pairing law.

* `circleDensityDifference_shift_tendsto` identifies the integral of a
  continuous deterministic shift against the signed annular densities with
  the limit `Real.circleAverage g z r - Real.circleAverage g 0 r`.
* `IsWholePlaneGFF.exists_localPairing_tests_with_shift_limit` supplies the
  **same** local mean-zero tests for the centered GFF circle in probability
  and, for every continuous deterministic shift, its centered circle average.
  The latter is a deterministic limit, and the former is obtained from the
  actual covariance error.
* `tendstoInMeasure_normalizedMass_of_fixedShift_approximation` lifts any
  measurable finite-scale normalized decoder to the actual normalized LQG
  limit under `IsLQGMeasure`, circle continuity, bounded exhaustion,
  continuity-set, and nonzero/finite mass hypotheses. It does not infer the
  LQG limit or the finite-scale decoder.
* `exists_fixedShift_normalizedMass_decoder_of_common_limits` and
  `fixedShift_event_representation_of_mass_decoder` turn common finite-scale
  limits into one measurable decoder and then into the two event
  representations required by `cone_event_pos_of_smooth_shift`, for events
  measurable in a countable family of normalized masses. The latter event
  measurability and sufficiency for the actual cone event remain to be shown.

The concrete remaining circle step is: for each `r > 0`, buffered measurable
`E`, and smooth `g`, construct one jointly measurable `D` as in
`IsWholePlaneGFF.exists_localPairing_centeredCircle_decoder`, such that its
second evaluation on
`fun φ => hC ω φ.1.1 + ∫ x, φ.1.1 x * g x` equals, for almost every `ω`
and volume-almost every `z ∈ E`, the centered circle average of
`addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) g`. The unshifted
evaluation must also have the existing decoder's equality. Local smooth-shift
absolute continuity is available from `local_smooth_shift_pairing_law`; it
concerns pairing laws alone and is not the desired circle-pairing domination.
The annular limit above is the deterministic ingredient for proving this
step, not a proof of the joint decoder's translation compatibility.

Once that step is established for each dyadic scale, use
`normalizedRestriction_lqgApprox_eq_of_centered_ae` to obtain the common
finite-scale normalized decoder, and apply the limit theorem above to both
actual LQG limits. The insertion `k` in the Section 11 transfer theorem also
needs explicit compatibility with the chosen local decoder. A countable
determining family, cone-event measurability in its normalized masses, and
positive-scaling invariance are still required for the concrete cone event.
None follows from fixed-test almost-everywhere equalities at random roots.

No new literature input is asserted. The unresolved step is Lean
infrastructure; a source-check of staged existence/volume-growth assumptions
remains required wherever those assumptions are used.
