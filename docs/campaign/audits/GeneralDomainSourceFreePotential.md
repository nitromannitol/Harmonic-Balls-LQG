# General-domain source-free potential

Task `general-domain-source-free-potential`: partial, not a proof of source-free harmonicity.
The potential-theoretic infrastructure used here is due to Leonardo Bonanno.

`integrable_greenFunction_of_compact_source` proves Bochner integrability at
all points of `V \ K`. `integrable_greenFunction_of_source_free_open` applies
this on a zero-mass open set by replacing `K` with the compact set `K \ U`.
Neither claim requires a growth estimate or Hölder regularity.

The unresolved kernel lemma is, with `open Set InnerProductSpace`:

```lean
∀ {V : Set ℂ}, IsOpen V → Bornology.IsBounded V →
  ∀ x y : ℂ, greenFunction V x y = greenFunction V y x
```

This is a mathematical theorem to prove from the existing definition, not an
additional literature assumption. `Section6.harmonicOnNhd_greenFunction_right`
proves harmonicity with a fixed first argument, whereas `greenPotential` varies
that argument. `greenFunction_ball_comm` proves reciprocity for discs only.
`GreenDomainExhaustion.tendsto_greenFunction_of_exhaustion` gives pointwise
convergence for general exhaustions but does not itself establish reciprocity
on the approximating domains. `Section6.exists_uniform_bound_greenFunction`
already provides the local uniform estimates on disjoint compact sets. Once
reciprocity is proved, dominated convergence and
`Section6.harmonicOnNhd_integral_of_circle_bounds` still need to be assembled.
No harmonicity, continuity, or numbered-result closure is claimed here.
