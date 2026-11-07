# Whole-plane observation source truncation

The declarations in `HarmonicBalls/Proofs/Potential/WholePlaneObservationTruncation.lean` are measure-theoretic helpers, not closures of numbered results. The potential-theoretic infrastructure uses work of Leonardo Bonanno.

For a finite source measure carried by a compact set and a locally finite observation measure with positive-power upper growth on every sufficiently small ball, `wholePlane_observation_kernel_integrable_product` proves integrability of the actual whole-plane Green kernel in source-observer order on every bounded observer set. It encloses source and observer sets in a disc and invokes `log_integrable_product_of_upper`; the Newton kernel normalization is retained, including its totalized diagonal value.

`wholePlane_observation_source_integrability` records the source-integrability events for the full and every restricted measure and the observer-integrability of their potentials. `wholePlane_observation_source_truncation_on` proves almost-everywhere convergence and convergence of the integral of the absolute difference over any bounded observer set, for measurable increasing source sets whose union carries the source measure. Its proof uses dominated convergence first in the source and then in the observer. `wholePlane_observation_source_truncation_ae` covers the plane with a countable family of balls. No global L1 claim is made.

Verification: lock-free Lean check and project module build; the four declarations print only `propext`, `Classical.choice`, and `Quot.sound` as axioms. The Lean file contains no forbidden proof placeholders or elevated heartbeat setting. No new literature input is introduced.
