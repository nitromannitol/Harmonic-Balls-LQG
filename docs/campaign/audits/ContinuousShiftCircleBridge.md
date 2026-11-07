# Continuous shift circle bridge audit

`shiftedReconstructedGFF` is the reconstructed normalized distribution plus
`ofCont` of the actual continuous sample path. Pointwise measurability and
continuous paths give a measurable continuous-map-valued witness. Subtracting
that witness recovers the reconstructed whole-plane GFF exactly; no independence
is assumed.

For each fixed positive radius and center, Bonanno's almost-sure convergence of
mollified GFF circle averages and the deterministic continuous-function limit
justify the circle-average identity. The fixed-circle raw `hcirc` equality is
transferred from `BonannoNormalizedVersion`. Exceptional events may depend on
the circle. The centered identity subtracts the shifted field's unit-circle
average, which is the continuous function's unit-circle average almost surely.
No unrestricted additivity of `circleAvg` is used.

No literature premise or numbered-result closure is introduced. The printed
axioms are `propext`, `Classical.choice`, and `Quot.sound` only; the source
contains no forbidden proof escape.
