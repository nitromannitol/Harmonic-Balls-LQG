# Finite-disc Green reciprocity: partial audit

The work uses the potential-theoretic infrastructure of Leonardo Bonanno.
`greenFunction_finite_disc_union_eq_isolated_disc` proves that an isolated
member disc has the same Green kernel after adjoining the remaining discs.
`greenFunction_pairwise_disjoint_finite_discs_comm` consequently establishes
reciprocity for a finite pairwise disjoint family, with arbitrary radii and all
values of both arguments (including exterior and diagonal values).

This does not establish the finite-disc premise of
`greenFunction_reciprocity_of_finite_disc_reciprocity`: intersecting discs may
belong to the same component, so the disjoint-component theorem cannot be
applied. A sufficient missing inductive implication, stated here only as a
proof target, is:

```lean
∀ (A : Set ℂ) (r : A → ℝ) (F : Finset A) (a : A),
  (∀ b ∈ F, 0 < r b) → 0 < r a →
  (∀ x y : ℂ, greenFunction (⋃ b ∈ F, Metric.ball (b : ℂ) (r b)) x y =
    greenFunction (⋃ b ∈ F, Metric.ball (b : ℂ) (r b)) y x) →
  ∀ x y : ℂ,
    greenFunction (⋃ b ∈ insert a F, Metric.ball (b : ℂ) (r b)) x y =
      greenFunction (⋃ b ∈ insert a F, Metric.ball (b : ℂ) (r b)) y x
```

The searched killed-process APIs provide occupation and resolvent formulas;
a proved symmetry of the killed Brownian kernel and its identification with
this greatest-harmonic-minorant Green function were not found. A smooth-boundary
Green-identity argument would also need to address overlapping discs and their
corners and tangencies. Neither route is assumed here.
