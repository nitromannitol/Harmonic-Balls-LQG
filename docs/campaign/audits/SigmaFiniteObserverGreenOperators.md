# Green operators for sigma-finite sources

The source measure is sigma-finite and supported almost everywhere in the bounded open domain. The observer is locally finite and satisfies the local upper-growth assumption. Neither finite source mass nor a weighted-kernel or reciprocity hypothesis is assumed.

`existsUnique_sigmaFinite_integrable_density_observer_L1_operator` applies the sigma-finite integrable-density product and observer estimates to construct a bounded linear map. Its characterization holds for every almost everywhere representative; extensionality gives uniqueness. Its bound is uniform over domains in the prescribed disc and supported source measures.

`existsUnique_sigmaFinite_observer_green_Linfinity_operator` constructs the row operator using the existing pointwise Green row estimate. Product-section measurability and the essential-supremum bound work with sigma-finite source measures. The operator has the corresponding representative characterization, uniqueness and uniform bound.

`sigmaFinite_observer_green_Linfinity_duality` obtains signed mixed-kernel integrability by multiplying the sigma-finite density product by an essentially bounded observer, then applies Fubini. Both sides retain the source-first Green orientation and the original diagonal convention. This does not assert reciprocity, pointwise normal representatives, boundary closure, or a numbered result.

This deterministic potential-theoretic infrastructure uses work of Leonardo Bonanno. No new literature input is introduced. The three declarations print only `propext`, `Classical.choice`, and `Quot.sound`. The file check and module build pass, and the forbidden-code scan is clean.
