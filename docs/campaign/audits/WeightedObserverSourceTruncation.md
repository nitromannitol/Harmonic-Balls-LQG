# Weighted source and observer truncation

`weighted_transposedGreen_joint_truncation` is deterministic infrastructure,
not a numbered-result closure. The bounded open domain is fixed. The finite
source measure is almost everywhere carried by the domain, and the locally
finite observer measure satisfies the existing local positive-power upper
growth condition. Source densities are signed, measurable, uniformly bounded,
and converge almost everywhere. The measurable observer sets increase and
cover `μ.restrict V` almost everywhere. The kernel is literally
`greenFunction V y x`, with source first and its existing diagonal convention.

The weighted observation theorem supplies product integrability, integrable
observer potentials, pointwise convergence, and the source L¹ error. Eventual
membership in the observer sets gives joint pointwise convergence. The joint
L¹ error is bounded by the source L¹ error plus the L¹ error from exhausting
the limiting integrable potential. No convergence hypothesis or literature
input is added. The potential-theoretic infrastructure uses work of Leonardo
Bonanno. The theorem prints only `propext`, `Classical.choice`, and `Quot.sound`
as axioms.
