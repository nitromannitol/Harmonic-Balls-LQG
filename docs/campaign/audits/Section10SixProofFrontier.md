# Proposition 10.6: deterministic proof frontier

Audit snapshot: `22c4875f280b55856d44b00ac8f9b81f7c512c92` (other workers' subsequent changes are not covered). This is a dependency audit, not a proof, source admission, or a 10.7 export audit. All Lean declarations mentioned as results are existing theorems; numbered results and staged inputs remain hypotheses where indicated.

## Source and binders

| Source object | Lean representation and scope |
| --- | --- |
| Fixed `γ, α₀`, probability space, GFF and LQG measure | `Draft/Section10.lean:103`: universally quantified, with `0 < γ`, `γ < 2`, `α₀ < lqgQ γ`, `IsWholePlaneGFF`, and `IsLQGMeasureOfField`. |
| Sample, time, pole | One `∀ᵐ ω ∂P` event, then **all** `t > 0` and `z ∈ ball 0 1`; not an event depending on `t` or `z`. |
| `G = Λ_t(z)`, `K = closure G` | `cluster (μ ω) 1 z t`, with `K ⊆ ball 0 1`; `G` is open and connected on the relevant I2 event. |
| `U`, `Γ` | Every `U ∈ connectedComponentsIn Kᶜ`, with `Γ = frontier U`; components are `connectedComponentIn F '' F` (`Defs/Geometry.lean:113`). |
| Target | `IsSimpleLoop Γ`: a continuous injective `Circle → ℂ` with range `Γ` (`Defs/Geometry.lean:92`). |
| Local connectivity and cut point | `IsLocallyConnectedSet Γ` (`Defs/Geometry.lean:103`); `IsCutPoint Γ a` means `a ∈ Γ ∧ ¬ IsPreconnected (Γ \ {a})` (`Defs/Geometry.lean:108`). |
| Separation witnesses | `x ∈ G`, `y ∈ U`, and `y ∈ connectedComponentIn Aᶜ x` means A does not separate these points. `a` is a putative frontier cut point, not the pole. |

The source proof at `paper/lqg_harmonic_ball-corrected.tex:2627` takes components of the **whole-plane** complement, although its proposition at :2623 still prints `B_1`. E17 (`~/paper-fleets/hb/ESCALATIONS.md:80`) records why the printed outer-component statement fails. The frozen C16 target uses the proof's whole-plane reading (`Draft/Section10.lean:92`); this audit follows that frozen target, not the printed domain. The corrected TeX at this snapshot still displays the old domain; do not silently identify the two.

## Paper proof and available carving

1. Source :2632–2658 argues for local connectivity using bounded crossings (10.1) and crossing containment (10.5). `Proofs/Sec10/ExistenceLocalConnectivity.lean:22` proves a conditional *different but useful* conclusion: locally connected `K` and `Uᶜ`, plus `U = Kᶜ` and equality of frontiers. Its explicit inputs are `LQGVolumeGrowthAllScalesStmt` (I2), **universal zero-strength** `LQGMeasureExistence P γ 0 hC hcirc` (staged), and frozen `CrossingComponentContainsClusterCrossingStmt` (10.5). It does **not** state `IsLocallyConnectedSet (frontier U)`; the passage to frontier local connectivity remains to be justified. Its 10.1-type input is obtained internally from I2 and staged zero-strength existence, not unconditionally.
2. Source :2660–2680 invokes a conformal boundary map, cut-point fibers and a separation argument. `Proofs/Sec10/FrontierMinimalSeparation.lean:36` establishes the key proper-closed-subset reconnection from open connected `G`, open connected `U`, and `frontier U ⊆ frontier G`. Its conditional cluster specialization is :95 and uses I2. `Proofs/Sec10/ConnectedCutPointPieces.lean:66` decomposes any compact connected set with a cut point into two proper compact connected pieces meeting only at that point; :86 combines this with the cluster geometry, assuming I2 and `IsPreconnected (frontier U)`, to produce compact connected `A`, `B` whose union separates `x` and `y` although neither piece does. The nonempty `G` and `U`, compactness and frontier connectedness must be supplied when applying this result; the latter is not a consequence of the local-connectivity theorem's *stated* output alone.
3. `FrontierTwoComponents.lean:72` identifies exactly two complementary components, and `FrontierDeletionConnectivity.lean:69` shows deletion of any nonempty frontier part yields connected complement, both conditional on I2 and 10.5. They do not themselves establish no cut points or a Jordan parametrization. `LoopCutPointFibers.lean:68` proves the **opposite direction**, simple loop implies no cut points. None of these results proves 10.6.
4. Source :2632 cites Pommerenke, *Boundary Behaviour of Conformal Maps*, Theorem 2.6 for the Jordan conclusion and :2661 cites Theorem 2.1 for boundary extension. A separate correctly quantified planar Jordan characterization, including all required hypotheses and the unbounded exterior case, remains to be proved or supplied as a properly sourced explicit literature hypothesis. The source's notation at :2666–2674 switches between `ψ` and `φ` and uses `0` without establishing `0 ∈ G`; use an arbitrary `x ∈ G`. Its displayed map `B_1 → U` also needs care for unbounded `U` (the paper's sphere interpretation may place infinity in the target). These observations do not establish the theorem false.

## First missing deterministic implication on this route

The following exact component-form type is the singleton-intersection planar separation principle (a special case of Janiszewski):

```lean
∀ (A B : Set ℂ) (a x y : ℂ),
  IsCompact A → IsCompact B → A ∩ B = {a} →
  y ∈ connectedComponentIn Aᶜ x →
  y ∈ connectedComponentIn Bᶜ x →
  y ∈ connectedComponentIn (A ∪ B)ᶜ x
```

This is the first missing implication **after** the already-proved cut-point obstruction above, not a claim that it is the only possible route. The result of `ConnectedCutPointPieces.lean:86` supplies all its hypotheses and the negation of its conclusion, hence would yield no cut points once its own hypotheses and a common event are supplied. `Proofs/Sec10/JaniszewskiPathBridge.lean:45` proves only equivalence with the corresponding `JoinedIn` path formulation, explicitly **not either formulation**; :16 already bridges paths and connected components in open sets. No proof of this principle was found in bounded searches of project Lean files, Mathlib, MarkovProcess or elliptic_regularity. The requested `~/lean/subdiffusive-process` path was absent on sandbox; no claim about that repository is made.

**Bounded next task:** prove the displayed singleton-intersection principle in a new deterministic Section 10 topology file, reusing `singleton_separation_path_iff_component` and its path lemmas. Check the precise published theorem and its sphere/plane and endpoint hypotheses before using any source; do not introduce a new input or assume it as a theorem. Then, in a separate assembly, intersect the existing I2 event, provide `frontier U` connectedness and witnesses, and derive the conditional no-cut conclusion. This task alone does not establish the missing boundary-local-connectivity or Jordan-characterization steps, nor does it discharge I2, 10.5, or staged LQG existence.

## E41 dependency warning

`Proofs/Sec10/CrossingImpliesNoHoles.lean:77` proves I2 + frozen 10.5 imply `IsConnected (closure G)ᶜ` simultaneously for compactly contained clusters; `UniqueComplementFrontier.lean:20` consequently identifies **every** `U` with the full complement. This materially strengthens the local-connectivity route and is not an unconditional predecessor. E41 (`~/paper-fleets/hb/ESCALATIONS.md:200`) gives a deterministic annular open-set example where the general topological reading of 10.5 fails, and explains that the LQG cluster assumptions may matter; it is **not** an LQG counterexample. The paper's 10.5 rectangle and `int(Uᶜ)` argument at `paper/lqg_harmonic_ball-corrected.tex:2594` needs independent scrutiny under those cluster assumptions. E41 does not invalidate the displayed abstract singleton-separation implication or the I2-only obstruction, but it prevents presenting the 10.5-dependent local-connectivity/no-hole chain as proved without that premise. E17/C16 affects which `U` is quantified, not the abstract separation implication.
