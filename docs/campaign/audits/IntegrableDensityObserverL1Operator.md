# Integrable-density observer L¹ operator

`existsUnique_integrable_density_observer_L1_operator` constructs the unique continuous real-linear map from L¹ of a finite source measure to L¹ of a locally finite observer restricted to the bounded open domain. The observer satisfies local upper ball growth; the source lies in the domain almost everywhere. The nonnegative operator bound is uniform over subdomains of the fixed disc and source measures, with the observer and its growth fixed.

The map is represented observer-almost-everywhere by the literal signed Green potential, with source first and observer second. Its characterization also holds for every source-almost-everywhere representative, without a measurability assumption on that representative: integral congruence applies at each observer point. Product integrability supplies the almost-everywhere integrable slices needed for addition; the observer bound gives continuity and the operator norm estimate. Extensionality and the representation give uniqueness.

This is analytic infrastructure, not closure of a numbered paper result. The potential-theoretic infrastructure uses work of Leonardo Bonanno. The declaration prints only `propext`, `Classical.choice`, and `Quot.sound` as axioms. The file-level check and module build pass; the forbidden-code scan is clean.
