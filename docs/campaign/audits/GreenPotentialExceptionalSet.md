# Green potential exceptional set: partial audit

The potential-theoretic infrastructure uses work of Leonardo Bonanno.

`green_disc_integrable_product_of_upper` proves product integrability on an
enclosing disc under the local positive-power upper bound, without excluding
atoms of the finite source. It uses the disc Green estimate and a uniform Riesz
potential bound; `ae_measure_singleton_eq_zero_of_upper` removes the diagonal.

`ae_greenPotential_of_local_upper_growth` transfers disc integrability to a
bounded open subdomain by Green domain monotonicity. It proves that the real
kernel is source-integrable at almost every observation point and identifies
the real potential with the finite lower integral whose diagonal value is
infinite. `ae_greenPotential_sub_of_local_upper_growth` gives the corresponding
identity for two sources. No boundary regularity or source-observation
separation is assumed.

Still required: product integrability of the general-domain Green kernel in
observation-source order. The disc product bound supplies domination. The
available `aestronglyMeasurable_greenFunction_prod_of_compact` applies when the
first marginal is compactly concentrated inside the domain; an exhaustion or
other construction must extend it to the bounded observation restriction.
This is unfinished proof work, not a claim that the mathematical result fails.
No numbered paper result is closed here and no new literature input is used.
