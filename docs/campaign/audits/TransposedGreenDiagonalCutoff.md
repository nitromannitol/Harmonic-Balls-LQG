# Transposed Green diagonal cutoff

`transposedGreen_diagonal_cutoff` is deterministic approximation infrastructure,
not a numbered-result closure. For a bounded open domain, a finite source
almost everywhere in the domain, and a locally finite observer with the stated
local positive-power upper growth, it uses the literal source-first kernel
`greenFunction V y x` and the restricted observer measure. It proves joint
measurability and product integrability for each distance cutoff, simultaneous
source-slice integrability and convergence at almost every observer, and
observer L¹ convergence. It assumes only that the real cutoff radii tend to
zero; positivity is unnecessary, including on the diagonal because the Green
function there is zero.

The existing mixed integrability theorem bounds the indicators. Away from the
diagonal the cutoffs eventually equal the kernel; on the diagonal both are
zero. Dominated convergence is applied first to the source and then to the
observer, using twice the integral of the absolute kernel as the observer
bound. No uniform convergence, continuous representative, or literature input
is asserted. The potential-theoretic infrastructure uses work of Leonardo
Bonanno. The printed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
