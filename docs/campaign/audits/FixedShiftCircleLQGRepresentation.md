# Fixed smooth shifts: circle and normalized-mass representation

`HarmonicBalls.Proofs.GFF.FixedShiftCircleLQGRepresentation` provides fixed
deterministic-shift infrastructure for Lemma 11.8. It uses the actual
whole-plane GFF joint Gaussian and covariance assumptions, local circle
decoders, and the local Cameron–Martin theorem; no joint circle/pairing law
or decoder universality is assumed. The imported Cameron–Martin theorem is
Leonardo Bonanno's work.

`circleDensityDifference_shift_tendsto` proves the deterministic limit of
the signed annular tests. `IsWholePlaneGFF.exists_localPairing_tests_with_shift_limit`
constructs a single local test sequence for which the GFF pairing converges
in probability to the centered circle and the pairing against any continuous
deterministic shift converges to its centered circle average.
`decoder_add_shift_of_pairing_law` transfers decoder equality along the local
pairing-law absolute continuity using this actual approximation sequence.
`IsWholePlaneGFF.ae_shifted_centeredCircle_decoder_at` applies it to every
deterministic buffered circle; `IsWholePlaneGFF.ae_ae_shifted_centeredCircle_decoder`
uses joint measurability and Fubini to obtain the needed sample/center
almost-everywhere equality. No random-root conclusion is inferred.

`IsWholePlaneGFF.exists_fixedShift_normalizedLQGApprox` constructs one
measurable family of normalized circle approximations for both the original
field and its fixed smooth shift. The shift is continuous globally and smooth
on a ball larger than the local pairing ball; the approximation sets must be
measurable and buffered there. `IsWholePlaneGFF.exists_fixedShift_normalizedMass_decoder`
lifts these common approximations to one measurable decoder of countably many
normalized masses of the **actual** two LQG limits. Its explicit hypotheses
are `IsLQGMeasureOfField` for the original field, `IsLQGMeasure` for the
shifted circle process, a bounded monotone buffered exhaustion of the local
ball, almost-sure continuity-set conditions for both measures, and nonzero
finite mass on the ball. No staged existence or volume-growth input is
asserted by the theorem; callers must supply and source-check such inputs if
used to discharge its hypotheses.

`fixedShift_event_representation_with_insertion` turns any measurable event
in those countably many decoded normalized masses into the two local pairing
representations required by `cone_event_pos_of_smooth_shift`; it absorbs the
arbitrary fixed deterministic insertion `k` in that theorem by translating the
decoder's input. `coneMassEvent_smul_iff` proves the actual cone mass event is
invariant under any nonzero finite global rescaling of its measure.

For h5's final cone-event assembly, the remaining precise obligation is to
exhibit a countable family `A : ι → Set ℂ` and a measurable set
`C : Set (ι → ℝ)` such that, for both actual measures almost surely,
`coneMassEvent μ Q M r z ↔ (fun i => (normalizedRestriction μ U (A i)).toReal) ∈ C`,
with the relevant cone and Green-potential supports inside `U`, and verify
the exhaustion/continuity-set/positive-finite-mass hypotheses. The scaling
lemma above supplies the algebra for passing from the normalized restriction
to the unnormalized cone event once that locality and measurability are
proved. The generic representation theorem then supplies both `hE` and `hEp`.
This file does not claim cone-event measurability, positive probability,
uniformity in centers or scales, or a numbered-result closure.
