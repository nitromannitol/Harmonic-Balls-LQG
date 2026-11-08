# Continuous circle profile and dyadic approximations

The decoder evaluates a continuous positive-radius circle profile at each dyadic radius, subtracts the deterministic logarithmic circle average, and applies the existing measurable LQG approximation decoder. Its equality with the approximation of `circleProfile` holds for every continuous profile and every index. The logarithmic correction uses `fieldCircleAverage_eq` at positive radius.

The joint affine law is the pushforward of `IsWholePlaneGFF.identDistrib_continuousCircleAffine` under the measurable map pairing the profile with its entire decoded sequence. This preserves dependence between the profile and the sequence. The affine transformation acts on the profile; this result asserts neither spatial covariance of measures nor a limiting LQG measure law.

The raw identification uses `IsWholePlaneGFF.ae_circle_map_eq_raw` and `ae_lqgApprox_circleProfile_eq`, giving equality for all dyadic indices on one event. No additional literature premise is introduced. The GFF and continuous circle-average construction are due to Leonardo Bonanno.

The lock-free Lean check passed. The printed axioms of the decoder, measurability, pointwise identity, joint law, and raw identification are `propext`, `Classical.choice`, and `Quot.sound` only.
