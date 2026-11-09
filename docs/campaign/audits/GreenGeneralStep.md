# Audit: GreenPotentialGeneralStep (steps4-final Section 1), worker q2, round 1

Target: `HarmonicBalls/Steps/Sec2/GreenPotentialGeneral.lean:24` (`GreenPotentialGeneralStep`), consumer
`HarmonicBalls/Proofs/Sec2/GreenPotentialGeneral.lean:18`. Source: `notes/wpn-steps4/steps4-final.tex` Section 1,
lines 29-284 (Stage 1: lines 125-199; Stage 2: lines 200-284).

## Stage 1 (lines 125-199): formalized, `HarmonicBalls/Proofs/Potential/GreenGeneralBoundary.lean`

Checked by hand before formalizing; all steps hold for the Lean statements.
- Barrier (l.137-151): with the exterior-sphere inequality `d² + ½|x-z|² ≤ |x-w|²` (z3 lemma
  `exists_half_radius_geometry_of_isSmoothBoundedOpen`), `b(x) = log(|x-w|/d)` satisfies
  `c|x-z|² ≤ b(x) ≤ |x-z|/d` on the closure, `c = 1/(4d²(1+T²/(2d²)))`. Formal: `barrier_bounds`.
- Boundary modulus (l.152-160 + barrier comparison): `|Hg(x) - g(z)| ≤ C|x-z|^κ`, `κ = a/(a+2)`, `s = |x-z|^{1/(a+2)}`.
  Formal: `boundary_modulus`, `upper_barrier_bound`, `rpow_identities`.
- Global Hölder (l.162-199): the paper uses a case split with an interior gradient estimate
  (`|∇Hg| ≤ 2B/dist`, cited as GT (2.31)). The formal proof replaces it by the translation argument:
  `w(p) = u(p+e) - u(p)` is harmonic on `U ∩ (U-e)`, and on its frontier `|w| ≤ C|e|^κ` by the boundary modulus.
  The weak maximum principle then gives the bound everywhere. No gradient or divergence-theorem input is needed.
  Formal: `holder_of_boundary_modulus`, using `le_of_frontier_le` (proved from the mean value property of
  Mathlib, `InnerProductSpace.HarmonicOnNhd.circleAverage_eq`, applied to `v + ε‖x‖²`).
- Components: the Gilbarg-Trudinger solution is applied to each component `connectedComponentIn O x`
  (`exists_dirichlet_holderOnWith`). Uniqueness comes from the maximum principle. Cross-component pairs are
  handled by a boundary point on the segment (`exists_frontier_mem_segment`).
- Literature input: `GilbargTrudingerThm2_14` (`HarmonicBalls/Proposed/GilbargTrudinger.lean`), Gilbarg-Trudinger,
  Theorem 2.14, p. 26, as a Prop hypothesis. Its wording is taken from the brief and must be source-checked by the
  operator against the book; it has not been checked here.

## Stage 2 (lines 200-284): identification and consumer

- The defined kernel is `greenFunction O x y = N(x,y) - I_O[N^e(x,·)](y)` (`Defs/Green.lean:70`). Formally,
  `I_O[N^e(x,·)]` is the Dirichlet solution with data `N(x,·)` on `∂O` (planned, not yet formalized).
- Integrability (l.200-216, the inequality `0 ≤ G ≤ N(x,·) - min_{∂O} N(x,·)`) does not need symmetry.
- GAP (not closed). The paper's formula at l.268, `G_O(x,y) = N(x,y) - ∫N(ξ,y) ω_x(dξ)`, equals the Lean
  `greenFunction O y x`, not `greenFunction O x y` (the Lean convention: pole in the first slot, minorant evaluated
  in the second). Passing from that formula to the Hölder claim (l.276-284, `q = V - H[V|∂O]`) needs the symmetry
  `greenFunction O x y = greenFunction O y x` for `x, y ∈ O`. Steps4 l.272-273 justify it by "the bounded-domain
  Green-identity argument given in the audited round-3 Section 1". The audit (`notes/wpn-steps4/AUDIT-steps4-t1.md`
  l.25 and l.127) identifies the source as `steps3.tex` Section 1, lines 166-173 and 190-196 (exhaustion of a
  component by smooth bounded domains, then Green's identity). That source is not in this repository, and the
  symmetry is not in Mathlib or in `Proofs/`. Its Lean type, and the missing input, is
  `greenFunction_symm_of_isSmoothBoundedOpen {O : Set ℂ} (hO : IsSmoothBoundedOpen O) {x y : ℂ} (hx : x ∈ O)
  (hy : y ∈ O) : greenFunction O x y = greenFunction O y x`.
  Without it, the Hölder conclusion of `GreenPotentialGeneralStep` is not reached by this route.
- The consumer `greenPotentialHolderStmt_of_volumeGrowth` depends on `GreenPotentialGeneralStep` and is not closed.

## Forbidden-token and build status

- Raw scan of the two owned files: clean (no `sorry`, `axiom`, `admit`, `native_decide`, `maxHeartbeats`,
  `unsafe`, `extern`, `implemented_by`, `set_option`, `opaque`).
- `lc` passes on `GreenGeneralBoundary.lean` and `GilbargTrudinger.lean`. `lb` build is recorded in the report.
