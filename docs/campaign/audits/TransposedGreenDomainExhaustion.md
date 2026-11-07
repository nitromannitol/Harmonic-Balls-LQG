# Transposed Green potentials along domain exhaustions

`HarmonicBalls.ae_tendsto_transposedGreenPotential_of_exhaustion` proves
convergence at almost every observer in a bounded open domain, for a finite
source concentrated there and any monotone open exhaustion. The kernels retain
the literal source-first order. The diagonal is treated using the prescribed
zero value, including for atomic sources.

`HarmonicBalls.tendsto_integral_norm_transposedGreenPotential_sub_of_exhaustion`
proves convergence in integral norm over the domain. The proof uses domain
monotonicity and product integrability to obtain integrability of each
approximating potential and domination by the limiting potential. Dominated
convergence is applied first in the source and then in the observer variable.
The almost-everywhere qualification avoids claims at exceptional observers
where totalized integrals can conceal nonintegrability.

The analytic helper uses Leonardo Bonanno's potential-theoretic work, does not
use Green reciprocity, and introduces no literature assumptions or numbered
result closure. Lean reports only `propext`, `Classical.choice`, and
`Quot.sound`.
