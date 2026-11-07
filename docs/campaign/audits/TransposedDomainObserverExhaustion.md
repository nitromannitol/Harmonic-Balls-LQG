# Transposed domain exhaustion for observers

`transposedGreenPotential_observer_exhaustion` is deterministic infrastructure,
not a numbered-result closure. The domains are monotone, open, and exhaust a
bounded open domain `U`; the finite source is almost everywhere carried by `U`.
The locally finite observer satisfies the existing local positive-power upper
growth condition. All observer assertions use `μ.restrict U`, and the literal
kernel has source first: `greenFunction (V n) y x`.

Product integrability on `U` and kernel monotonicity provide integrability of
all approximating kernels, their almost-everywhere source slices, and their
observer potentials. Dominated convergence in the source gives almost-everywhere
convergence; dominated convergence in the observer gives integral-norm
convergence. On the diagonal the literal kernels are zero, while off the
diagonal the domain-exhaustion theorem applies. No reciprocity or new literature
premise is used. The potential-theoretic infrastructure uses work of Leonardo
Bonanno. The three declarations print only `propext`, `Classical.choice`, and
`Quot.sound` as axioms.
