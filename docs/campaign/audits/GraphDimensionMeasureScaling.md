# Graph dimension under mass normalization

`HarmonicBalls/Proofs/Sec2/GraphDimensionMeasureScaling.lean` proves equality of graph covers and distances after multiplying a measure by `ENNReal.ofReal c` for positive `c`, with threshold `ε / c`. The argument uses the extended-nonnegative-real division inequality, so it also covers infinite ball masses.

The dimension equivalence follows by composing the existing full-scale interpolation limit with the positive scaling of the threshold and proving that the ratio of logarithmic denominators tends to one. Finiteness at every positive dyadic threshold is obtained directly from the graph-distance equality and the original dimension hypothesis. Applying the reciprocal normalization gives the converse.

No literature premise or identification of the physical LQG dimension is introduced. The printed axioms for the distance equality, forward implication, and equivalence are `propext`, `Classical.choice`, and `Quot.sound`.
