# Bounded-domain Green reciprocity: unresolved finite-disc identity

Task `bounded-domain-green-reciprocity` remains blocked. No general reciprocity
or symmetric occupation representation has been proved. The potential-theoretic
sweeping and exhaustion infrastructure cited below is due to Leonardo Bonanno.

A precise sufficient missing identity, for the existing `greenFunction`, is:

```lean
∀ (ι : Type) (F : Finset ι) (c : ι → ℂ) (r : ι → ℝ),
  ∀ x y : ℂ,
    greenFunction (⋃ i ∈ F, Metric.ball (c i) (r i)) x y =
      greenFunction (⋃ i ∈ F, Metric.ball (c i) (r i)) y x
```

This is a derived theorem to prove, not a proposed literature input. Its
substantive case is overlapping discs: the existing disjoint-union result does
not handle those. One possible route is to construct symmetric approximating
kernels for such a union and identify their limit with the greatest-minorant
Green function; neither the construction nor its identification is available
in the cited results.

Why this suffices: `exists_finite_disc_open_exhaustion` in
`Proofs/Potential/GreenRegularDomainExhaustion.lean` constructs a monotone
exhaustion by finite disc unions of any open set. For distinct `x,y` in a
bounded open set, `tendsto_greenFunction_of_exhaustion` in
`Proofs/Potential/GreenDomainExhaustion.lean` gives convergence in both orders;
uniqueness of limits then transfers the missing identity. The exterior and
diagonal cases follow directly from `greenFunction_of_notMem_left`,
`greenFunction_of_notMem_right`, and `greenFunction_self` in `Defs/Green.lean`.

Existing `greenFunction_ball_comm` covers discs centred at zero and
`greenFunction_translate` transfers that to arbitrary discs. The theorem
`greenFunction_eq_of_disjoint_open_union_all` handles only disjoint unions.
`Section6.harmonicOnNhd_greenFunction_right` gives off-pole harmonicity in the
second variable; it does not establish symmetry or harmonicity in the pole.
The balayage in `Proofs/Sec4/GreenBalayage.lean` gives a correction identity
under its specific measure and Newtonian potential hypotheses, not the missing
union formula. MarkovProcess has killed occupation/resolvent infrastructure,
but the searches found no symmetric killed kernel identity identified with
this greatest-minorant Green function. EllipticRegularity's Green construction
is stated for balls and dimension at least three, so is not a direct planar
arbitrary-domain result. The requested local subdiffusive-process checkout was
not present under `~/lean`.
