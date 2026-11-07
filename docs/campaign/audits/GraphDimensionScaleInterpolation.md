# Graph-dimension scale interpolation

`IsLiouvilleGraphDimension.fullScale` proves that the dyadic graph-distance
exponent in `HarmonicBalls/Defs/LQGGraphDistance.lean` converges along all
positive mass thresholds tending to zero, with the same limit `1 / dimension`.
Together with `isLiouvilleGraphDimension_of_fullScale`, this gives the
converse interpolation between the two formulations.

The proof uses monotonicity of graph distance, adjacent dyadic intervals,
and the ratio of successive dyadic logarithmic scales. It proves that any
path cover has at least one ball and establishes finite distance at **every**
positive threshold from eventual dyadic finiteness, before applying
`ENat.toNat_le_toNat`. The adjacent logarithmic bounds are then squeezed
using the two dyadic exponent limits. No additional literature input is used.

This is a deterministic statement about the existing graph-distance
definition. It does not establish the LQG dimension characterization or
admit any pending literature input. Leonardo Bonanno contributed to the
formalization.
