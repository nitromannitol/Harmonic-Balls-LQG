# Background charge and parameter recovery

`HarmonicBalls/Proofs/GFF/BackgroundChargeParameter.lean` proves the deterministic algebra for `lqgQ` in `HarmonicBalls/Defs/Notation.lean`, matching equation (Q) of the corrected paper. The difference identity factors `lqgQ a - lqgQ b` as `(b - a) * (4 - a * b) / (2 * a * b)`. Positivity for `0 < a < b < 2` yields strict decrease and injectivity on `(0, 2)`.

The recovery theorems take equality of the two background charges as an explicit hypothesis. Equality of the products `ξ * lqgQ γ` and `ξ₀ * lqgQ γ₀` then identifies the Weyl exponents because the common charge is positive. The combined corollary instantiates `ξ₀` as `γ₀ / d`, the normalization in equation (xi) of the corrected paper. The real number `d` is arbitrary; no dimension existence, metric identification, or scaling identity is inferred here. In a physical application those identities and the interpretation of `d` must be established independently.

This file acknowledges Leonardo Bonanno's GFF construction and adds no literature input or numbered-result closure. The source scan finds no prohibited proof placeholders or axioms. All seven printed axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`.
