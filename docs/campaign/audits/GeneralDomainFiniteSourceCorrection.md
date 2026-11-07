# General-domain finite-source harmonic correction

`HarmonicBalls.exists_harmonic_generalDomain_transposed_correction` constructs a
harmonic function on an arbitrary bounded open planar domain for a finite source
concentrated on a compact subset. At volume-almost every observer it proves
integrability of the literal source kernels `newtonKernel y x` and
`greenFunction V y x`, together with the stated integrated correction identity.

The proof uses the jointly measurable compact-pole balayage representative with
zero measure and mass, its compact-observer bounds, and harmonicity of the
greatest harmonic minorant. Dominated convergence and the harmonic integral
theorem give harmonicity. The existing logarithmic exceptional-set theorem and
general-domain product integrability supply the almost-everywhere conditions;
the diagonal is removed using the atom conclusion. Newton kernel symmetry is
used only to identify the whole-plane potential. No Green reciprocity is used.
The empty compact set is handled separately in the representative construction.

This analytic helper uses Leonardo Bonanno's potential-theoretic work and does
not assert closure of a numbered paper result. No literature assumptions are
introduced. Lean reports only `propext`, `Classical.choice`, and `Quot.sound`.
