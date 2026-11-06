# Green kernels under exhaustion

`HarmonicBalls/Proofs/Potential/GreenDomainExhaustion.lean` proves convergence
for a monotone open exhaustion of a bounded open planar set and arbitrary pole
and evaluation point in the union, away from the diagonal. No regularity of
the union boundary or of the exhaustion is used. Closure nesting implies the
required monotonicity, and both points eventually belong to the domains.
The kernels themselves increase at every pair, including early junk-value stages.

The substantive limit identification was already established in
`HarmonicBalls/Proofs/Sec5/ExhaustionClusterCompatibility.lean`:
`tendsto_greenFunction_of_open_exhaustion` uses convergence of greatest
harmonic minorants via Poisson sweeping and assumes the pole lies in the first
domain. The new result shifts the exhaustion to the first domain containing
the pole and transfers convergence back to the original sequence. It supplies
`exists_greenRegular_exhaustion_with_kernel_limit` using the existing regular
exhaustion theorem. Its regularity condition concerns the chosen pole.

This result gives no numbered paper-result closure and asserts no boundary
regularity for the larger domain.
