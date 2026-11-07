# Weighted observation stability

`weighted_transposedGreen_observation_stability` proves mixed product integrability for every density in a uniformly bounded measurable sequence and its bounded measurable limit. The source is a finite measure concentrated almost everywhere in the bounded open domain, and the locally finite observation measure satisfies the stated local positive-power upper growth condition.

The proof uses `generalDomain_green_integrable_product_of_local_upper_growth` for the literal kernel `greenFunction V y x` under the product of the source and the restricted observation measure. Pointwise domination yields the weighted mixed integrability. Fubini gives source-slice integrability for almost every observer, where dominated convergence applies to the source integral. A second dominated-convergence argument uses the integrated absolute kernel as an observation-side majorant and proves convergence of the integral of the absolute difference. The exceptional observer set may depend on the domain, source, and densities; no planar null set is transferred to the observation measure and no reciprocity is used.

This is a deterministic approximation lemma, not a numbered-result closure or a literature input. The printed axioms are `propext`, `Classical.choice`, and `Quot.sound`. The potential-theoretic infrastructure uses work of Leonardo Bonanno.
