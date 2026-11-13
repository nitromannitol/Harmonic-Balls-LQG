# Section 8 conditional export audit

2026-11-05. **Conditional composition: PASS. Source/semantic verdict: OPEN.**
These are conditional provider applications, not proofs of numbered results.
This bounded review is not a recursive semantic approval of all field,
obstacle, Green-function, or annulus definitions, nor a source check of the
staged LQG inputs.

## Identity and scope

Frozen targets: `HarmonicBalls/Draft/Section8.lean:55,96`, respectively
`BoundaryMeasureZeroOfCompactClusterStmt` (8.1) and
`OriginManyGoodScalesStmt` (8.3); 8.2 is `TypicalPointManyGoodScalesStmt` at
`:74`. They are Prop definitions, not sealed theorem exports. `FROZEN.md:3–13,65–67`
records approval at `bd58fe6`; the current whole-file SHA-256 is
`8ac734605b6668208a7641a1ae4a5ec7b4aa9288deb69ebcecfcfad3db80cf7a`,
identical to that commit. The frozen register has no per-declaration hash or
provider binding, so this is a whole-file identity check, not a complete
manifest audit.

The advertised corrected and preserved source files both hash to
`8fdbb03043011800560e4d947eb79a3cfdd7cc8767a3af94469f04201b7593fc`;
`CORRECTIONS.md:4` says none have been inserted. E49 is unresolved. We compare
literal TeX `2119–2170,2209–2260` plus the separately recorded decisions, not
pretend the artifact includes C1/C23. E25 (`ESCALATIONS.md:126–131`) asks for a
ruling on the stronger G28 order; `inbox.md:45–46` only says noted for freeze
review. The frozen register approves the declarations generally; we found no
separate explicit resolution of the particular printed-versus-stronger E25
question. E50 remains open for the dependence of 6.6 witnesses on βminus.

## Expanded binder review

`archive/HarmonicBalls/Audit/Section8ConditionalExports.lean` expands the bodies of all
seven 8.3 provider premises and all three 8.1 provider premises, as well as both
conclusions, and applies the actual providers. The table classifies each
logical block of the **frozen result**, not the extra provider premises. SOURCE
means explicit source statement/standing setup; RULED means an operator
correction or a recorded frozen reading that requires source reconciliation;
TYPING means Lean carrier/realization. STANDING is folded into SOURCE here only
for the table counts; it is distinguished in the individual row.

| Frozen binder or result block | 8.1 | 8.3 | Basis and scope |
|---|---|---|---|
| `γ`, `0 < γ < 2`, `α₀ < Q` | SOURCE | SOURCE | standing setup, TeX 373–380 |
| `Ω`, measurable space, `P`, `hC`, `hcirc`, `μ` | TYPING | TYPING | arbitrary realization, not new analytic assumptions |
| GFF structure and LQG-measure predicate | STANDING | STANDING | TeX 356–396; bodies `Defs/GFF.lean:93`, `Defs/LQG.lean:53,63,73` |
| `βminus > (2+γ)²/2` | — | RULED/open | Draft 29–31, 90–95; C1 and E50 context; not explicit in the 8.3 printed binder |
| `C₃ > 0` before `ζ > 0`, `b ∈ (0,1)` | — | RULED/open | Draft 32–37; E25/G28, TeX 2160–2162 only gives one existential block |
| `a`, positive C's, `N₁ ≥ 1`, then every `N₀ ≥ N₁` and `m > 0` | — | RULED/open | same G28 discrepancy; `m` and parameters appear in TeX 2161, not this stronger order |
| one `P`-a.e. event, eventually in `N` | — | SOURCE | TeX 2161–2162 and 2153–2156; count is over `[N+1,2N]` |
| one `P`-a.e. event, then all `t > 0`, `z ∈ B₁` | RULED/open | — | printed `t` is unbound, TeX 2122–2126; simultaneous reading comes from proof 2230–2260 |
| `closure (cluster ...) ⊆ B₁`, zero frontier mass | SOURCE | — | TeX 2124; closed bounded subsets of ℂ are compact |

Block counts: 8.1 SOURCE 2, STANDING 1, TYPING 1, RULED/open 1,
EXCESS 0; 8.3 SOURCE 2, STANDING 1, TYPING 1, RULED/open 3, EXCESS 0.
These counts concern frozen top-level blocks and are **not** a passing recursive
five-bin audit; the RULED/open label does not assert an explicit E25 decision.
For the conditional providers every displayed earlier theorem or staged LQG
premise is EXCESS relative to the standalone source result. The 8.3 provider has
seven such premises and the 8.1 provider three; none is silently discharged by
the two composition examples.

Carrier/event observations: `hC` accepts all `ℂ → ℝ` functions, but the GFF
structure constrains pairings only for admissible test functions and circle
averages for positive radii. Its centered Gaussian covariance and continuous
circle-average modification are specified in `Defs/GFF.lean:93–109`.
`IsLQGMeasureOfField` is an a.s. dyadic vague-limit and locally finite measure
condition, not an unconditional construction; no claim of complete field
semantic equivalence is made. Both targets quantify the singularity for every
`α₀ < Q`, including negative values. 8.3 fixes all parameters before the
probability-space and field binders; the exceptional event is inside those
binders and is uniform in large N. 8.1 uses one event before both t and z,
and its compact-containment premise is retained for each pair.

The annulus count (`Defs/Annuli.lean:96–107`) uses exactly `N+1 ≤ n ≤ 2N`, the
very-good event and comparison. `IsVeryGoodAnnulus` (`:81–90`) includes all
three VG clauses and the absolute lattice; `IsGoodAnnulus` (`:47–52`) uses the
C23 corrected exit ordering, in contrast with the unreconciled TeX at
1119–1121. The Green supremum uses an infinite diagonal (`:68–71`). The
normalization of ENNReal division, endpoint conventions, and comparison with
the source require the pending deep semantic review; compilation does not
settle them.

## Actual premise consumption and status

* `OriginExplicitInputAssembly.lean:19–45` passes `hholder` (the Green clause
  of 2.5), `hgrowth` (I2), nonatomicity at α₀ = 0, affine invariance, coordinate
  change at every α₀, existence at α₀ = 0 and Weyl scaling at α₀ = 0. It obtains
  I1/full support from I2 (`Steps/Sec2/VolumeGrowth.lean:220`), passes I1 and
  I2 and all seven displayed inputs into the 6.7 probability route
  (`Proofs/Sec6/GoodPrevalenceBall.lean:69`), and specializes coordinate change
  at zero there. It also passes affine invariance and arbitrary-α coordinate
  change to `originManyGoodScalesStmt_of_coordinate_change`. The latter uses
  proved planar Brownian point avoidance (`OriginStatementPointPolarity.lean:28`)
  and the proved field germ triviality (`OriginGermAssembly.lean:43–55`,
  `OriginGermZeroOne.lean:82`); these are bridges, not extra staged inputs.
  Birkhoff is supplied by Leonardo Bonanno's proved LatticeProb port
  (`BirkhoffPort.lean:18`), not a retained `PointwiseBirkhoff` premise.
* I2 and I1 are derived claims, not literature axioms. The alternate
  `OriginLiteratureAssembly.lean:18–46` constructs I2 from Ding–Gwynne's staged
  `WholePlaneLQGBallMassBounds`, affine invariance, coordinate change at zero,
  Weyl scaling, existence and nonatomicity (there all α); it still retains the
  Green clause. `Proposed/LQG.lean:49,64,71,88,108` contains the other staged
  Props; each remains an explicit hypothesis pending operator source check.
  In particular an I2 producer is not evidence that the standalone provider
  is unconditional, and no 2.5 Green-clause producer was identified in this
  review.
* `ClusterBoundary.lean:89–121` consumes 3.2 only for openness, 6.11 for the
  component Harnack implication, and 8.2 for the typical-point count. It takes
  β = `(2+γ)²/2 + 1`, extracts `C₃` from 8.2, `b` from 6.11, the remaining
  parameters with ζ = 1/2 from 8.2, and `N₀ = max N₁ (N₁f ...)` before choosing
  α and m. It intersects the locally-finite, openness, Harnack, and good-scale
  events before introducing t and z. The deterministic bridge uses density and
  restricts from B₁ to the frontier using closure containment
  (`ClusterBoundary.lean:45–84`, `BoundaryDensity.lean:18–44`).
* 3.2 and 6.11 each have a proved I2-conditional producer
  (`Sec3/OpenLaplacian.lean:25`, `Sec6/VolumeGrowthConsequences.lean:19`). The
  additional Lean composition checks these exact applications while **keeping
  8.2 as a hypothesis**.

## Circularity and outstanding semantic obligations

A recursive project-import scan found 436 project modules reachable from the
8.3 provider and 20 from the 8.1 provider; none of their dependencies referenced
any of these provider exports: the audited 8.3 export and the audited 8.1
export. Direct proof tracing
also confirms the 8.1 assembly assumes 8.2 and the 8.3 assembly does not call
8.1 or 8.2. This is a bounded name/import search, not a full theorem-level
transitive dependency certificate, and it does not establish that all
mathematical routes are free of circular assumptions.

E48 remains a specific obstruction to deriving 8.2: the absolute δℤ² grid in
VG-iii changes phase under recentering (`ESCALATIONS.md:262–273`), so a single
origin statement does not immediately give a random-root statement. Required
work includes fixed-reference uniform phase frequency, measurable local
versions/identification, and the actual rooted-law comparison; the h1/h3
reports explicitly leave these open. DMS21 Lemma A.10 (arXiv:1409.7055v4
p.184) is the proposed source, but its exact normalization and applicability
must be checked and the required comparison proved or explicitly sourced;
see `~/paper-fleets/hb/INPUT-REQUESTS.md:58–102`. E49, E50, E25/G28,
staged-source checks, and recursive definition/assumption semantics remain
open. No 8.2 or unconditional numbered closure is asserted.

## Checks

`~/paper-fleets/hb/lc archive/HarmonicBalls/Audit/Section8ConditionalExports.lean`
and `~/paper-fleets/hb/lb HarmonicBalls.Audit.Section8ConditionalExports` pass.
Both provider `#print axioms` results are exactly `propext`,
`Classical.choice`, and `Quot.sound`; axiom closure does not eliminate explicit
premises. Placeholder scan of the owned Lean file is clean.
