# Observer Green L∞ adjoint

`bounded_observer_green_row` proves that an L∞ observer representative is integrable against each Green row for a source point in the domain, with a bound uniform over subdomains of the fixed disc. The observer is locally finite and has local upper ball growth.

`existsUnique_observer_green_Linfinity_operator` constructs the unique bounded real-linear map from L∞ of the restricted observer to L∞ of a finite source measure supported almost everywhere in the domain. Its norm has the uniform row bound. Its integral representation holds for every observer-almost-everywhere representative; no pointwise boundedness or measurability of that replacement is assumed. Addition uses the actual row integrability.

`observer_green_Linfinity_duality` proves the duality identity for any source-to-observer L¹ operator and observer-to-source L∞ operator with the indicated integral representations, including the operators constructed here and in `existsUnique_integrable_density_observer_L1_operator`. The signed mixed integrand is integrable by the existing integrable-density product theorem and the essential bound on the observer function. Fubini retains source-first Green orientation.

This is deterministic potential-theoretic infrastructure using work of Leonardo Bonanno; it does not close a numbered paper result. The three declarations print only `propext`, `Classical.choice`, and `Quot.sound` as axioms. The file-level check and module build pass; the forbidden-code scan is clean.
