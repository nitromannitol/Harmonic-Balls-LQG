# Completed origin germ

`IsWholePlaneGFF.completed_origin_germ_trivial` proves that an event has
probability zero or one when, for each positive radius separately, it is
almost surely equal to an event in the raw modulo-constant field
sigma-algebra on the corresponding ball. The result applies to an arbitrary
set, hence also to an ambient measurable event, and does not assume that the
ambient measurable space is complete. The quantifiers permit a different
representative and null set at each radius.

The generic `measure_zero_or_one_of_ae_local_germ` applies the existing
`exists_germ_measurable_event_of_ae_local` from
`Proofs/Sec8/AEGermTriviality.lean`: that lemma constructs one raw germ event
by a countable limsup of local representatives, using a decreasing cofinal
sequence and monotonicity. The specialization uses the existing dyadic
sequence and field sigma-algebra monotonicity, then applies
`IsWholePlaneGFF.origin_germ_trivial` from
`Proofs/Sec8/OriginGermZeroOne.lean` and measure invariance under a.e.
equality. The underlying theorem uses Leonardo Bonanno's LatticeProb
formalization.

This is an event-level conclusion on a given `IsWholePlaneGFF` realization;
it does not construct a rooted law, prove locality, or identify a common
samplewise representation of the field. No literature input is added.
