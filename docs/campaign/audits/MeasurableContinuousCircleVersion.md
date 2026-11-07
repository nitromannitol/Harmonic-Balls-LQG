# Measurable continuous circle-average versions

`HarmonicBalls/Proofs/GFF/MeasurableContinuousCircleVersion.lean` strengthens
Leonardo Bonanno's continuous circle-average version through the previously
checked `IsWholePlaneGFF.exists_continuous_circle_version`. The parameter space
is exactly `Set.Ioi (0 : ℝ) × ℂ`, and the target is its real-valued continuous
maps with the Borel compact-open measurable structure.

`aemeasurable_circle_map_of_evaluations` uses Mathlib's Borel/evaluation
characterization: the coordinate hypotheses imply null measurability, and the
countably generated target yields an almost-everywhere measurable map. The
null-measurable-space API is used in this proof; the resulting modification is
measurable on the original sample space. Subtracting its own unit-circle value
normalizes every sample, while the checked version ensures that this subtraction
changes the modification only on a null event. Raw agreement remains separately
almost everywhere for each fixed parameter.

Joint evaluation is continuous, so it is measurable in the sample and circle
parameter, including for measurable random positive radius and center. No raw
agreement at a random parameter is asserted. `ae_continuous_circle_map_eq`
uses a countable dense family and continuity to give a single almost-everywhere
equality of the continuous maps, following the checked uniqueness argument.

All printed axioms are `propext`, `Classical.choice`, and `Quot.sound`. No new
literature premise or change to a frozen declaration is introduced.
