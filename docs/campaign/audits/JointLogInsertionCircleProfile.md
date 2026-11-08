# Joint logarithmic insertion of continuous circle profiles

`logInsertedCircleProfile` is the continuous positive-radius profile obtained by subtracting `α * log (max r ‖z - v‖)`. Positivity of the radius makes the logarithm continuous even when the circle meets the insertion root. `circleAvg_logInsertion` proves the literal insertion correction for the distribution with coefficient `-α`.

The profile and its unit-circle normalization are jointly measurable in the original continuous profile, coefficient, and root. The random-parameter versions allow arbitrary dependence. From a single common raw-circle event, both formulas hold simultaneously for every coefficient, root, positive radius and center; the random-parameter corollaries preserve that quantifier order. `IsWholePlaneGFF.ae_circle_map_eq_raw` supplies this event for a whole-plane GFF and any coordinatewise continuous version.

The normalized formula subtracts the inserted profile's own unit-circle value. No simultaneous equality with the chosen circle average of a reconstructed distribution is asserted: the existing reconstructed-distribution theorem has fixed-circle scope. No literature premise is introduced. The GFF and continuous circle-average construction are due to Leonardo Bonanno.

The lock-free check and module build passed. The printed axioms of the measurability and common-event results are `propext`, `Classical.choice`, and `Quot.sound` only; the source scan for forbidden proof escapes is clean.
