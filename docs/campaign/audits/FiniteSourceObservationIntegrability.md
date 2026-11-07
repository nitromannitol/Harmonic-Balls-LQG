# Finite-source observation integrability

The declarations in `HarmonicBalls/Proofs/Potential/FiniteSourceObservationIntegrability.lean` are analytic helpers, not closures of numbered results. The potential-theoretic infrastructure uses work of Leonardo Bonanno.

`generalDomain_green_integrable_product_of_local_upper_growth` proves mixed absolute integrability of the actual Green kernel in source-observer order for a finite source concentrated almost everywhere in a bounded open domain, and a locally finite observer with all-local positive-power upper growth. A disc encloses the domain; the existing uniform disc estimate gives mixed integrability for the source restricted to its closed disc, which equals the source. Restriction of the observer measure and pointwise domain monotonicity yield the result. Joint measurability and the totalized diagonal are retained; no volume-null set is transferred to the observer.

`finiteSource_transposedGreen_observation_integrability` obtains observer-almost-everywhere source integrability and integrability of the literal Bochner transposed potential by product integration. `ae_lqg_finiteSource_transposedGreen_observation_integrability` derives both conclusions on one outer I2 event for all bounded open domains and finite sources; its observer exceptional set may depend on the choices. I2 remains an explicit hypothesis. No new literature input is introduced.

Verification: lock-free Lean check and project module build; all three declarations print only `propext`, `Classical.choice`, and `Quot.sound` as axioms. The Lean file contains no forbidden proof placeholders or elevated heartbeat setting.
