# Signed weighted transposed Green duality

`weighted_transposedGreen_fubini_duality` is deterministic infrastructure, not
closure of a numbered result. For a bounded open domain, a finite source almost
everywhere in the domain, and a locally finite observer with the stated local
positive-power upper growth, it treats bounded measurable real source and
observer densities. The kernel is literally `greenFunction V y x`, with the
observer measure restricted to the domain.

The existing mixed Green integrability theorem and boundedness give product
integrability for each singly weighted kernel and the doubly weighted kernel.
Fubini supplies both almost-everywhere slice assertions for the doubly weighted
kernel, the corresponding singly weighted slices, and both outer integrability
assertions. Pulling out the constant in each inner integral gives the signed
duality identity. The result makes no reciprocity or PDE assertion and adds no
literature premise. The potential-theoretic infrastructure uses work of
Leonardo Bonanno. The printed axioms are `propext`, `Classical.choice`, and
`Quot.sound`.
