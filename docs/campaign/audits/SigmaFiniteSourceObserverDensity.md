# Sigma-finite source densities observed by upper-growth measures

The source measure is sigma-finite and supported almost everywhere in the bounded open domain; the density is measurable and integrable. The observer measure is locally finite and satisfies the existing local upper-growth assumption. No finite source mass or weighted-kernel hypothesis is imposed.

`sigmaFinite_integrable_density_green_product_of_local_upper_growth` forms the finite measure `ν.withDensity (ENNReal.ofReal ∘ ‖f ·‖)`, applies the established finite-source product theorem, and converts back using `prod_withDensity_left` and `integrable_withDensity_iff_integrable_smul'`. Nonnegativity of the Green function dominates the signed kernel. `sigmaFinite_integrable_weighted_green_product_and_slices` applies this to `‖f‖` and obtains observer-almost-everywhere source-slice integrability by Fubini.

`sigmaFinite_integrable_density_observer_bound` uses the existing uniform Green row bound, product integrability and Fubini to obtain signed slices, observer integrability, and the uniform `C * ∫ ‖f‖` estimate. `tendsto_integral_norm_sigmaFinite_integrable_density_observer` applies the estimate to differences and uses the established slice integrability for integral subtraction. Source-first Green orientation and the original diagonal convention are retained.

This is deterministic potential-theoretic infrastructure using work of Leonardo Bonanno; it does not close a numbered paper result. No new literature input is introduced. The four declarations print only `propext`, `Classical.choice`, and `Quot.sound`. The file check and module build pass, and the forbidden-code scan is clean.
