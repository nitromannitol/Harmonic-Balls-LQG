# Log insertion circle averages audit

- Scope: `HarmonicBalls/Proofs/GFF/LogInsertionCircleAverages.lean` proves a helper for the actual distribution `logInsertionDistribution`; it does not close a numbered paper result.
- `mollAvg_logInsertion_eq_logPot` uses the distribution's test-pairing integral and the symmetry of distance. Leonardo Bonanno's `CircleAvg.logPot_circBump` supplies the Fubini identity, and his `abs_integral_bump_circLog_sub_le` supplies an error bound `(2⁻¹)^n / r`. His `circLog_eq_log_max` gives the stated circle mean. Positive `r` includes a circle through the insertion point and a circle centered at it.
- `tendsto_mollAvg_logInsertion` proves convergence of the actual mollified pairings before `circleAvg_logInsertion` invokes the chosen limit.
- `IsWholePlaneGFF.ae_circleAvg_reconstructedGFF_add_logInsertion` combines the insertion limit with Bonanno's almost-sure GFF mollifier convergence and the existing fixed-circle raw compatibility. Its exceptional set may depend on the insertion and circle. The unit-centered corollary uses the established normalization.
- No literature hypothesis is introduced, and no unrestricted additivity, joint exceptional set, or singular law transfer is asserted. Printed axioms for the four limit/circle declarations are `propext`, `Classical.choice`, and `Quot.sound`.
