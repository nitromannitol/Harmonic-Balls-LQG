# Observer Green total variation stability

For arbitrary finite source measures carried almost everywhere by an open planar domain contained in a fixed disc, the observed L¹ distance of the transposed Green potentials is at most a constant times the total variation mass of the signed difference. The observer is locally finite and satisfies the existing local upper-growth condition. The constant depends on the observer and enclosing disc, and is uniform in the domain and sources. The literal kernel is `greenFunction V y x`, source first, with its existing diagonal convention.

The sources are dominated by their sum. Their Radon–Nikodym derivatives are integrable; their difference represents the signed difference as a vector measure. Mathlib's variation theorem identifies its L¹ norm with the actual signed-measure total variation mass. Product and almost-everywhere slice integrability follow from the existing observer density bound, and source-slice integrability is established before the change of measure. Total variation convergence in real mass implies observed L¹ convergence. No reciprocity, weak convergence implication, new literature input, or numbered-result closure is claimed. The potential-theoretic infrastructure uses work of Leonardo Bonanno.

All three declarations print only `propext`, `Classical.choice`, and `Quot.sound`; the forbidden-code scan is clean.
