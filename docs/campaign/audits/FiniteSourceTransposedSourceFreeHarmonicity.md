# Finite-source transposed Green integral

The declarations in `HarmonicBalls/Proofs/Potential/FiniteSourceTransposedSourceFreeHarmonicity.lean` concern the literal kernel `greenFunction V y x`, in source-observer order. They do not establish a numbered result of the paper.

For bounded open `V`, a finite measure `ν` carried by `V`, and open `U ⊆ V` with `ν U = 0`, `harmonicOnNhd_transposed_greenIntegral_of_finite_source` proves harmonicity of the totalized Bochner integral on `U`; `continuousOn_transposed_greenIntegral_of_finite_source` gives continuity. No compact concentration inside `V`, Green reciprocity, or additional literature hypothesis is used.

The uniform bound uses the compact set `closure V \ U` only in an enclosing disc. For each compact observer set inside `U`, these two compact sets are disjoint. The existing disc Green bound and domain monotonicity bound the original kernel there. The proof uses the indicator of `V \ U` to obtain a jointly measurable family harmonic for every source, and uses finite-measure dominated convergence and the harmonic-integral circle criterion. The indicator agrees with the original integrand almost everywhere by the two measure assumptions.

The three declarations print only `propext`, `Classical.choice`, and `Quot.sound` as axioms. The potential-theoretic infrastructure is due to Leonardo Bonanno.
