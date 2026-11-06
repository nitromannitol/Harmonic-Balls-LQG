# Local cone mass representation: partial handoff

`ConeMassLocalRepresentation.lean` proves that the cone mass event depends
only on the measure restricted to a measurable set containing its cone
annulus and Green annulus. It proves measurability in the measure, using
`PinchGreenMeasurable.measurable_annulusGreenPotentialSup`: the latter uses
the lower semicontinuity of the actual extended Green kernel, including its
infinite diagonal, and a countable dense supremum with proved hypotheses.
It also proves equivalence with the event for a normalized restriction when
the normalizing mass is nonzero and finite.

`coneMassEvent_representation_of_measure_decoder` produces both event
representations, including any deterministic insertion, from a *common
measurable measure-valued decoder* of the two actual normalized restrictions.
It does not assume event measurability or an event representation.

Remaining: construct that common measure-valued decoder from the countable
real-mass decoder of `IsWholePlaneGFF.exists_fixedShift_normalizedMass_decoder`;
choose one continuity pi-system and buffered exhaustion valid for both
actual measures, and discharge both positive-finite-mass conditions. Relevant
existing ingredients include `exists_ae_continuity_piSystem_of_ae_locallyFinite`,
`exists_buffered_ball_exhaustion_of_ae_locallyFinite`,
`ae_frontiers_intersections_of_common_continuity`, and
`ae_referenceBall_pos_finite`. A joint construction for the two measures is
still required. The producer is not a proof of event positivity or a numbered
result. All four declarations use only `propext`, `Classical.choice`, and
`Quot.sound`; lc and lb pass.
