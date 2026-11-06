# Green potential exceptional set

The potential-theoretic infrastructure uses work of Leonardo Bonanno.

`green_integrable_product_restrict_of_local_upper_growth` proves product integrability
on arbitrary bounded observation restrictions for a finite compactly concentrated source and a
bounded open domain. Overlap of source and observation sets is allowed. The
proof dominates the nonnegative kernel by that of an enclosing disc. The disc
product bound follows from the existing quantitative Riesz and Green estimates.

`aestronglyMeasurable_greenFunction_prod_of_open` derives joint almost-everywhere
strong measurability for finite marginals, using compact exhaustion of the open
domain and the compact-first-marginal measurability theorem. The kernel vanishes
outside the domain. No symmetry of the general-domain Green function or boundary
regularity is assumed.

`ae_greenPotential_of_local_upper_growth` proves almost-everywhere source
integrability and removes the source atoms using the established diagonal-null
lemma. `greenKernelExtended` assigns infinity on the diagonal. At those
observation points its lower integral is finite and agrees with the real Green
potential. `ae_greenPotential_sub_of_local_upper_growth` proves the analogous
identity for a difference of two finite sources.

The source compact sets are not required to lie in the domain, a stronger form
than required. No numbered paper result is closed here and no new literature
input is used. Axiom checks for the exported results report only `propext`,
`Classical.choice`, and `Quot.sound`.
