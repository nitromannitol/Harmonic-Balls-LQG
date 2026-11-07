# Weighted whole-plane source Laplacian

The declarations in `HarmonicBalls/Proofs/Potential/WeightedWholePlaneLaplacian.lean` are potential-theoretic helpers; they do not close a numbered result. The potential-theoretic infrastructure uses work of Leonardo Bonanno.

For a bounded measurable real weight, `positiveSource` and `negativeSource` are the original finite measure weighted by `ENNReal.ofReal (max (f y) 0)` and `ENNReal.ofReal (max (-f y) 0)`. Their finiteness is proved from the bound, and absolute continuity retains compact carriage. Product integrability for each source gives a common almost-everywhere event on which both weighted slices are integrable. The density integral formula and integrable subtraction identify the literal weighted Newtonian integral with the difference of the positive potentials, respecting source-observer order and totalized diagonal values.

`hasLaplacian_weighted_wholePlane` establishes that common slice event and the distributional identity with positive argument `negativeSource` and negative argument `positiveSource`; the latter includes actual local integrability. The sign follows from the existing whole-plane positive-source Green-potential theorem. No new literature input or numbered closure is claimed.

Verification: lock-free Lean check and project module build pass. All seven declarations print only `propext`, `Classical.choice`, and `Quot.sound`; the Lean file has no forbidden proof placeholders or elevated heartbeat setting.
