# Graph-dimension triangle bound audit

Leonardo Bonanno contributed to the graph-distance formalization.

`IsLiouvilleGraphDimension.symm` preserves the existing dimension predicate
when the endpoints are reversed. `IsLiouvilleGraphDimension.min_le` assumes
that the same measure has dimensions `d₁`, `d₂`, and `d₃` between `z, v`,
`v, w`, and `z, w`, respectively, and proves `min d₁ d₂ ≤ d₃`. These are
consequences of the existing dyadic definition, not claims of existence or
endpoint independence, and introduce no literature premise.

The proof uses the triangle inequality in extended naturals and converts to
natural numbers only after establishing finiteness. Positivity of distance
allows logarithmic monotonicity. The bound by twice the maximum yields a
`1/n` correction, which tends to zero; positive dimensions then reverse the
reciprocal inequality. Symmetry uses symmetry of graph distance at each scale.

The lock-free check and module build pass. Both declarations print only
`propext`, `Classical.choice`, and `Quot.sound` as axioms. The Lean source
contains no `sorry`, `axiom`, `admit`, `native_decide`, or heartbeat override.
