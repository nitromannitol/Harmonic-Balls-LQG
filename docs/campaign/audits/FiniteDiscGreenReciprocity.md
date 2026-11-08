# Finite-disc Green reciprocity: partial audit

The work uses the potential-theoretic infrastructure of Leonardo Bonanno.
`greenFunction_finite_disc_union_eq_isolated_disc` proves that an isolated
member disc has the same Green kernel after adjoining the remaining discs.
`greenFunction_pairwise_disjoint_finite_discs_comm` consequently establishes
reciprocity for a finite pairwise disjoint family, with arbitrary radii and all
values of both arguments (including exterior and diagonal values). The theorem
`greenFunction_finite_discs_comm_of_intersections_contained` extends this to
families in which every intersecting pair is contained in a family disc. These
families may contain non-nested intersecting discs, but their union is still a
union of disjoint maximal discs. `greenFunction_laminar_finite_discs_comm`
covers the special case of disjoint-or-nested pairs.

`greenFunction_point_reflection` proves covariance under point reflection about
an arbitrary center, without a boundedness or openness assumption. As a
consequence, `greenFunction_point_reflection_pair_comm` proves reciprocity
at points exchanged by a central symmetry of the domain. In particular,
`greenFunction_two_congruent_discs_centres_comm` handles the two centres of
a congruent-disc union, including crossing outer boundaries. This does not
establish reciprocity at arbitrary pairs in that union.

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
this greatest-harmonic-minorant Green function were not found. The elliptic
regularity package has a weak duality identity for approximate Green functions
on balls (`PDE.Ch4Green.integral_mul_eq_integralAverage`); its H¹₀ weak-solution
objects have not been identified with the present Green function or extended
to the finite-disc domains. Its compact-support second identity likewise does
not itself provide the boundary terms or approximation needed for overlapping
discs. Neither route is assumed here.
