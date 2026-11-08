# Green pairing reciprocity for signed densities

`HarmonicBalls.green_reciprocal_pairing` treats a bounded open planar domain `V` and two real densities that are almost everywhere strongly measurable and essentially bounded on `V`. This includes bounded measurable compactly supported densities, without requiring compact support or support inside `V`: the pairing uses planar volume restricted to `V`. Neither kernel integrability nor reciprocity is assumed.

The result proves absolute integrability of `(x, y) ↦ f x * greenFunction V x y * g y` against the product of restricted planar volumes. It also proves almost-everywhere integrability of both actual Green potentials and integrability of the two outer weighted potentials. Fubini's theorem and `greenFunction_bounded_open_comm` then yield equality of the iterated Bochner integrals. The proof uses the existing Green product-integrability theorem, which transfers a disc-kernel estimate to the bounded domain. The kernel's established zero diagonal convention is retained; the pointwise reciprocity theorem includes the diagonal, so no separate removal of a null diagonal is required. The potential-theoretic infrastructure uses work of Leonardo Bonanno.

The standalone Lean check and module build passed. The theorem's printed axioms are `propext`, `Classical.choice`, and `Quot.sound`; the forbidden-code scan is clean.
