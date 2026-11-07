# Source-free transposed density stability

`weighted_transposed_green_L1_local_uniform` is a deterministic helper, not a
numbered-result closure. The bounded open domain is `V`, the open source-free
set `U` lies in `V`, and the observer set `L` is compact and contained in `U`.
The finite measure is carried by `V` and gives `U` zero mass. Densities are
real and Bochner integrable, with no boundedness or pointwise measurability
assumption; convergence is in the stated integral of absolute differences.
The Green kernel is `greenFunction V y x`, with source `y` first.

The source-free kernel bound yields integrability for each observer in `U` and
a common compact-set bound by the L¹ norm of the density. Applying it to the
difference gives uniform convergence. For harmonicity, the positive and negative
parts define finite absolutely continuous measures retaining both source null
sets. Their existing finite-source harmonic potentials differ on `U` by the
actual signed weighted integral, using Bochner integrability and the
with-density integral identity. Openness transfers this equality to neighborhoods.
No reciprocity or new literature hypothesis is used.

Lean's axiom print lists only `propext`, `Classical.choice`, and `Quot.sound`.
The potential-theoretic infrastructure uses work of Leonardo Bonanno.
