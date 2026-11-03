# Source dependency graph: Sections 1-5, 9 and Appendix A

Scope: every numbered result of Sections 1-5, 9 and Appendix A of arXiv:2208.11795. Sections 6-8 and 10-11 come in the
next task (inventory-graph-2); their results appear here only as providers or consumers. Numbering, labels and
`draft_name`s: `docs/campaign/INVENTORY.tsv`.

Conventions. Line numbers refer to `paper/lqg_harmonic_ball-corrected.tex`, which is still identical to the arXiv
source (no `% CORRECTION` yet). For each result:
- **Proof**: where the proof is printed.
- **Uses**: the numbered results and displayed equations the printed proof uses.
- **Lit**: literature facts, with the bbl keys resolved below.
- **Consumed by**: the `\ref` occurrences, given as consumer (line). These come from a script that maps each reference
  to its enclosing statement or proof. Uses found by reading but not referenced are marked *implicit*.
- **Issues**: references to the list at the end. Issues are labelled F (printed statement false or not established),
  G (gap in the proof, statement plausibly true) or S (slip or typo).

## Bibliography keys used (resolved in `paper/lqg_harmonic_ball.bbl`)

| key | reference | used for |
|---|---|---|
| DS11 `duplantier2011liouville` | Duplantier-Sheffield, LQG and KPZ, Invent. Math. 185 (2011) | Prop 2.1 (conformal covariance), Sec 3.1 (circle averages, BM) |
| SW16 `sheffield2016field` | Sheffield-Wang, field-measure correspondence commutes with all conformal maps (arXiv) | Fact 2.1 IV for all maps simultaneously |
| DDDF20 `ding2020tightness`; DFGPS20 `dubedat2020weak`; GM21 `gwynne2021existence` | LQG metric: tightness, weak metrics, existence and uniqueness | Fact 2.2 (no theorem numbers printed) |
| BG20 `berestycki2020random` | Berestycki-Gwynne, random walks on mated-CRT maps and LBM, CMP | Lemma A.1 there, adapted for Lemma 2.4 |
| Pon16 `ponce2016elliptic` | Ponce, Elliptic PDEs, measures and capacities, EMS Tracts 23 | Sec 16.2 / remark after Prop 13.5 (Campanato estimates); Prop 7.3 (weak normal derivative); Lemma 12.15 |
| Kig19 `kigami2019` | Kigami, Time changes of the Brownian motion, Mem. AMS 259 (2019) | Thm 13.1 (heat kernel), used for Prop 2.6 |
| AG01 `armitage2000classical` | Armitage-Gardiner, Classical potential theory | Thm 3.7.5 (lsc regularisation of an infimum of superharmonic functions), Thm 3.2.2 (characterisation of subharmonicity), Thm 4.3.8 (Laplacian of a potential), Sec 4 (Riesz decomposition) |
| SS13b `shahgholian2013harmonic`; Sak84 `sakai1984solutions` | Shahgholian-Sjodin 2013; Sakai 1984/85 | Thm 2.1 of SS13b, cited for Lemma 9.1 |
| Sak82 `sakai2006quadrature` | Sakai, Quadrature domains, LNM 934 | Thm 10.13 (model for the proof of Prop 5.6 only) |
| SS13a `ss-contour` | Schramm-Sheffield, contour line of the continuum GFF, PTRF 157 | Lemma 3.9 (terminology "local set" in Prop 1.3) |
| GM20b `gwynne2020local` | Gwynne-Miller, Local metrics of the GFF, Ann. Inst. Fourier 70 | Lemma 6.5. The paper prints no number; believed to be Lemma 3.1 there, unverified |
| Var17 `vargas2017lecture` | Vargas, lecture notes, Sec 2.1.1 | normalisation h^C_1(0)=0 of eq:cov-kernel |

## Shared unnumbered definitions (nodes used by many results)

- D1 harmonic ball, eq:harmonic-ball (78-81), with the enlarged test class eq:harmonic-fns (139-146). See F1.
- D2 polynomially high probability (338-339): P[E^r] >= 1 - O(r^p) for some p>0. Annulus A_{r1,r2}(z), eq:annulus (333).
- D3 the field: h = h^C - alpha0 log|.|, eq:gff (382); Q, eq:Q (374); law invariances eq:gff-scaling (368) and
  eq:h-coordinate-change (386, derived from eq:gff-scaling; it holds with the alpha0 term because the circle average of log|.| is log r).
- D4 the obstacle problem on B_r: supersolutions eq:super-solutions (583), least supersolution lambda, eq:least-super-solution (588),
  cluster Lambda, eq:non-co-set (592), odometer v, eq:limit-odometer (596-597; see S1).
- D5 subharmonic ball, eq:subharmonic-ball (742) with test functions eq:sub-harmonic-potential (746-751).
- D6 regularised cluster Lambda-hat = int(closure Lambda), eq:regular-cluster (846).
- D7 Appendix: volume growth eq:volume-growth (3526; S1), Green potential q_{B_R} eq:expected-exit-time (3532) with properties 1-4
  (3537-3541), obstacle beta_t eq:obstacle (3551), shifted supersolutions eq:shifted-supersolutions (3556), f_t eq:lsc-leastsuperharmonic (3594).
- D8 reflected LBM heat kernel, eq:defining-property-of-kernel (546-547; S1).

## Implicit inputs (used without a number)

- I1 **Full support of mu_h**: a.s. mu_h(U)>0 for every non-empty open U. The paper states it informally at lines 134-135. It is used in
  the repair of Prop 4.1 (G3), in Prop 5.6 (mu_h(B)>0, 2465-2470), Lemma 9.3 Step 3 (2382-2383), Lemma 9.4 (2399-2408) and the repair of G7.
  It is not among the items of Fact 2.1. Derivable from the lower bound of Lemma 2.4 (Borel-Cantelli over dyadic eps) plus
  scaling (eq:h-coordinate-change, Fact 2.1 III-IV), or a GMC literature fact (would need an External).
- I2 **A.s. volume growth for all small r and all z in B_R** (eq:volume-growth). The paper says it "follows from Lemma 2.4 and the
  scaling properties" (3529-3530). This needs Borel-Cantelli over dyadic scales and monotonicity in r. Used by all of App A,
  by Prop 2.5 and by Lemma 4.2.
- I3 t -> h^C_{e^t}(0) has a continuous modification that is a standard BM (DS11 Sec 3.1). Used in the proof of Thm 5.5 (995-1004).
- I4 Classical potential theory: minimum principle and strong maximum principle; the Poisson integral on discs; Weyl's lemma
  (a continuous function with distributional Laplacian <= 0 is superharmonic); symmetry G(x,y)=G(y,x); the 2D dilation
  invariance of the distributional Laplacian, used in Lemma 5.7. AG01 is cited for some of these.
- I5 **Lewy-Stampacchia inequality / inverse maximum principle** (e.g. Dupaigne-Ponce 2004; Pon16). It is **not cited**, yet needed
  for nu >= 0 in Lemma 3.2 (G1).

## Section 1

### 1.1 Theorem (theorem:harmonic-balls, 152): ExistenceUniquenessHarmonicBallsStmt
- Proof: no proof environment. Assembled at 863-878 and 977: existence from Thm 5.5, uniqueness from Prop 5.6.
- Uses: Thm 5.5, Prop 5.6; D1, D6.
- Lit: none directly.
- Consumed by: Thm 1.2 (171); the phrase "conditions of Theorem 1.1" in Prop 5.4 (855), Thm 5.5 (865), Prop 5.6 (875) and Sec 9 (2278, 2392, 2410).
- Issues: F1 (the literal test class makes the theorem false), G7 (left Hausdorff-continuity is never proved), S1 (Lambda_t(x) at 156).

### 1.2 Theorem (theorem:harmonic-balls-properties, 170): HarmonicBallNoveltyStmt
- Proof: no proof environment. The outline (306-314) assembles it from Prop 10.7 (Jordan boundaries, with Lemma 10.1),
  Prop 11.2 (not Lipschitz, via Lemma 11.5) and Prop 11.11 (not LQG-metric balls). The detailed graph is in the next task.
- Uses: Props 10.6-10.7, 11.2, 11.11; Thm 1.1 (statement).
- Consumed by: none.

### 1.3 Prop (prop:locally-determined, 179): HarmonicBallLocalSetStmt
- Proof: 1031-1042.
- Uses: Lemma 5.8 (1037), giving eq:cluster-coincides (1038); Fact 2.1 II locality (1036). If z is not in U the event is null. Reduction
  to bounded U by exhaustion: the closure is compact, so {closure Lambda-hat subset U} = union_n {closure Lambda-hat subset U_n}.
- Lit: SS13a Lemma 3.9 is cited for terminology only. The Lean statement should be the "i.e." clause (180-181).
- Consumed by: none (only text, 810 and 1014).
- Issues: G9 (Lemma 5.8 for arbitrary U; smooth U_n suffice here), S1 (t >= 0 at 180, but Lambda_0 is undefined).

## Section 2

### 2.1 Fact (fact:lqg-measure, 401): LiouvilleMeasureFactStmt
- Proof: cited (418-420). Items I-III are "immediate from" eq:measure-lim (DS11/SW16 construction). Item IV is DS11 Prop 2.1 for a
  fixed map and SW16 for all maps simultaneously.
- Consumed by: Lemma 5.7 (916, items III-IV), Prop 1.3 (1036, item II), Lemma 6.4 (1204, 1220), Lemma 6.7 (1327), Lemma 8.3 (2164),
  Lemma 8.2 (2215), Lemma 11.8 (2863), Lemma 11.10 (3001), Lemma 11.16 (3416); implicitly App A (3530, scaling) and I1/I2.
- Lean: External. Cut it into its four items so that each proof takes only what it uses.

### 2.2 Fact (fact:lqg-metric, 432): LQGMetricFactStmt
- Proof: cited (455-456): DDDF20, DFGPS20, GM21. The paper prints no theorem numbers. The definition of xi uses d_gamma (gp-kpz Cor 1.7).
- Consumed by: Lemma 11.15 (3363), Lemma 11.16 (3416); Sec 11 metric-ball arguments. Not used in Sections 1-5, 9 or A.
- Issues: S1 ("z in C" for z in the complex plane, 448).

### 2.3 Prop (prop:green-properties, 480): GreenFunctionBallStmt
- Proof: none ("standard properties", 479). The explicit formula G_{B_R}(x,y) = (2 pi)^{-1} log(|R^2 - conj(x) y| / (R |x-y|)) gives all four items.
- Consumed by: Lemma 4.3 (765). Implicitly: Lemma A.6 (Delta G = -delta at 3873), Lemma 9.1 (superharmonicity of G at 2297),
  App A property 3 of q (3540), Prop 4.1, Lemma 5.7 (G_{B_k}(kz,kx) = G_{B_1}(z,x) at 920).
- Lean: paper-owned, standard. Check whether EllipticRegularityLean already provides the Green function of the ball.

### 2.4 Lemma (lemma:volume-growth, 497): LiouvilleVolumeGrowthStmt
- Proof: 509-515. For eq:ball-volume the proof says "exactly the same argument as [BG20, Lemma A.1]" and gives no other proof.
  eq:ann-volume is derived from eq:ball-volume via B_{(r2-r1)eps/4}(z + (r1+r2)eps/2 e_1) subset A_{r1 eps,r2 eps}(z) subset B_{r2 eps}(z).
- Lit: BG20 Lemma A.1.
- Consumed by: Prop 2.5 (534-535), Prop 2.6 (558), Sec 6 text (1128, 1132), Lemma 6.7 (1353), Lemma 6.13 statement (1715),
  Prop 7.1 (1983, 1985), Prop 7.2 statement (2027) and proof (2033), App A via I2 (3529).
- Issues:
  - F2: the printed exponent range is false at z=0 for alpha0 > 2 or alpha0 < -2.
  - G10: an a.s. version for all scales is needed downstream.
  - Minor: in eq:ann-volume the centre z + ((r1+r2)/2) eps e_1 may leave B_1, where eq:ball-volume says nothing; use B_2 by scaling.

### 2.5 Prop (prop:lbm-exit-time, 524): GreenPotentialLiouvilleHolderStmt
- Proof: 533-537, a sketch. Finiteness from Lemma 2.4; Hoelder continuity from the Campanato-to-Hoelder embedding (Pon16 Sec 16.2,
  remark after Prop 13.5) with Lemma 2.4 (upper bound only, a Morrey condition mu(B_r(x)) <= C r^{beta+}).
- Consumed by: Prop 4.1 (710), Lemma 4.2 (732), Sec 6 text (1138), App A property 1 of q (3543). Implicitly: Lemma 4.3 (bounded
  potentials for Fubini), Prop 9.2 (continuity of f - tG), Lemma 9.3 (continuity of u).
- Issues:
  - G10: needs I2, i.e. an a.s. statement for all small r and all centres in closure(O). Lemma 2.4 covers only B_1.
  - The statement omits "a.s." and the measure of the L^infty space (mu_h).
  - G4: Lemma 4.2 needs a quantitative version (Hoelder seminorm <= C(h,O) ||f||_infty), which the statement does not give.

### 2.6 Prop (prop:lbm-continuity, 554): ReflectedLBMHeatKernelStmt
- Proof: 557-561. Kig19 Thm 13.1 with input Lemma 2.4, plus "a scaling argument" from the unit square to any square.
- Lit: Kig19 Thm 13.1. Earlier continuity results (AK16, MRVZ16) are mentioned at 540.
- Consumed by: Lemma 6.4 (1234) only.
- Issues: S1 at 547. `p^K_t(x,y) dy` must be `p^K_t(x,y) mu_h|_K(dy)`: mu_h is singular w.r.t. Lebesgue measure, so the law of the
  LBM at time t has no Lebesgue density with a positive continuous kernel. The kernel is relative to the speed measure mu_h.

## Section 3 (statements only; proofs in Appendix A)

The appendix proves everything for a deterministic Radon measure mu satisfying eq:volume-growth on B_R, with R=1 and z=0
"for notational simplicity" (3547). Translation: lambda = s~ - q_{B_1} (3576-3578). Instantiating mu = mu_h needs I2.

### 3.1 Lemma (lemma:basic-properties, 621): LeastSupersolutionMemStmt
- Proof: Lemma A.1 (3587-3589), via lambda = s~ - q (Delta lambda = Delta s~ + mu <= mu).
- Uses: A.1, D7, I2.
- Consumed by: Prop 4.1 (701), Lemma 5.7 (916). Implicitly: Props 9.2 and 4.1 (minimality of lambda).

### 3.2 Lemma (lemma:non-coincidence-open-harmonic, 627): ClusterOpenLaplacianStmt
- Proof: Lemmas A.1 and A.2 (3650-3651).
- Uses: A.1, A.2. The decomposition with nu also needs I5 (not cited).
- Consumed by: Lemma 4.2 (731), Lemma 4.3 (765), Lemma 6.8 (1411, 1423), Lemma 6.9 (1478), Lemma 6.10 (1528), Lemma 10.1 (2515),
  Lemma 10.5 (2611), Prop 10.6 (2677).
- Issues: G1. nu <= mu_h follows from superharmonicity. nu >= 0 is asserted but never proved.

### 3.3 Lemma (lemma:monotonicity, 644): ClusterMonotoneStmt
- Proof: Lemma A.3 (3730).
- Consumed by: Prop 7.1 (1991), Prop 7.2 (2059), proof of Props 5.1-5.2 (2113); implicitly Prop 5.6 (eq:cluster-monotonicity, 2423).
- Issues: S1 (the superscript drops ";z", 645).

### 3.4 Lemma (lemma:conservation-of-mass, 649): ClusterConservationOfMassStmt
- Proof: Lemmas A.4 and A.5 (3769).
- Consumed by: Prop 4.1 (712), Lemma 4.3 (765), Prop 7.1 (1992, 2000), Prop 7.2 (2058, 2086). Implicitly: Lemma 4.2 (lambda=0 on
  the boundary of B_1), Prop 5.4 (mu_h(Lambda-hat)=t), Prop 9.2 (2323).
- Issues: S1 (mu for mu_h at 651); G1 (the first claim mu_h(Lambda) <= t uses nu >= 0).

### 3.5 Lemma (lemma:cluster-compatibility, 657): ClusterCompatibilityStmt
- Proof: Lemma A.6 (3832).
- Consumed by: Thm 5.5 proof (968), Lemma 5.8 proof (1024); Sec 5 text (861, 1016-1017).

## Section 4

### 4.1 Prop (prop:lower-bound, 673): ClusterLowerBoundStmt
- Proof: 691-713.
- Uses:
  - Lemma 3.1 (Delta lambda <= mu_h, 701); with the minimum principle, lambda >= -q_1 where q_1 is the exit time of LBM from B_1.
  - Prop 2.5 (q_1 finite, 710); eq:lower-bound-green (707).
  - Lemma 3.4 for t^+ = mu_h(B_1) (711-712).
- Consumed by: Prop 5.4 text (850), Prop 7.2 (2042), proof of Props 5.1-5.2 (2107), Lemma 10.1 (2515), Lemma A.2 (3665, a forward
  remark only).
- Issues: G3 (the t^+ step does not follow from Lemma 3.4 as stated); S1 (t log|x-z| in place of -t G_{B_1}(z,x) at 704-708;
  eps depends on z).

### 4.2 Lemma (odometer:cont, 721): LeastSupersolutionHolderStmt
- Proof: 730-733. lambda^z_t is minus the G_{B_1}-potential of sigma = mu_h|_Lambda + nu|_{boundary Lambda}, which has density in [0,1]
  w.r.t. mu_h (Lemma 3.2), and lambda=0 on the boundary of B_1 (Lemma 3.4). Then apply Prop 2.5.
- Uses: Lemma 3.2 (731), Prop 2.5 (732), Lemma 3.4 (implicit).
- Consumed by: no `\ref` anywhere in the paper. Implicit uses in Sections 6-7 go to the next task.
- Issues: F3 (alpha must depend on alpha0); G4 (C uniform in t and z needs a quantitative Prop 2.5); G1.

### 4.3 Lemma (lemma:harmonic-ball, 755): ClusterSubharmonicBallStmt
- Proof: 764-789.
- Uses:
  - Lemmas 3.4 and 3.2 and Prop 2.3 (765), giving eq:v-characterization (766-771) with nu=0 because mu_h(boundary)=0 and nu <= mu_h.
  - Integration by parts on a smooth Lambda' with closure(Lambda) subset Lambda' subset O, giving the mean value for harmonic q.
  - Fubini, and the Riesz decomposition (AG01 Sec 4, 761).
- Consumed by: Prop 5.4 text (850); Thm 5.5 ("each cluster is a subharmonic ball"); the outline (290).
- Issues: G5 (integration restricted to Lambda; "v(z)" at 785); F1 (the remark at 753 is false for the literal test class).

## Section 5

### 5.1 Prop (prop:upper-bound, 815): ClusterUpperBoundStmt
- Proof: 2101-2102, "immediately" from Prop 7.1. Polynomially high probability as T->0 gives existence of T a.s., since the events increase as T decreases.
- Consumed by: Prop 5.4 text (849-850); Thm 5.5 through Prop 5.4.

### 5.2 Prop (prop:continuity, 824): ClusterContinuityStmt
- Proof: 2101-2114.
  - eq:continuity (831) from Prop 7.2 (2104).
  - eq:contains-origin (826): Prop 7.1 with Borel-Cantelli over r_n = 2^{-n} (2108-2111), Prop 4.1 (2107) and Lemma 3.3 (2113).
- Consumed by: Prop 5.4 text (849-850). Implicitly: Prop 5.6 (repair G8) and Thm 1.1(b).
- Issues: G12 (scope); S1 ("+ B_eps(z)" at 832 should be "+ B_eps").

### 5.3 Prop (prop:boundary-measure, 836): ClusterBoundaryMeasureZeroStmt
- Proof: Section 8, Prop 8.1 (2122-2127). No `\ref` links them.
- Consumed by: Prop 5.4 text (849-850); Prop 9.2 (implicitly, through mu_h(Lambda-hat)=t).
- Issues: S1. "closure subset B_r(z)" with r free (837) must read "subset B_1", as Prop 8.1 states at 2124.
  - Read as "for all r", it would claim mu_h(boundary Lambda^z_t)=0 for clusters touching the boundary of B_1, which Section 8 does not prove.
  - Read as "for some r", the hypothesis is vacuous.

### 5.4 Prop (prop:conditional, 853): RegularizedClusterHarmonicBallsStmt
- Proof: the paragraph 846-851.
  - Lambda subset Lambda-hat and mu_h(Lambda-hat \ Lambda) = 0 by Prop 5.3, so Lambda-hat is a subharmonic ball (its test class is
    smaller than that of Lambda, and the closures agree).
  - Then combine Prop 4.1, Lemma 4.3 and Props 5.1-5.3. Implicitly: Lemma 3.2 (connected), Lemma 3.4 (mass t), Prop 7.2 (closure
    at the exit time meets the boundary).
- Consumed by: Thm 5.5 proof (952).
- Issues: F4 (T unbound or uniform in z; free binder r).

### 5.5 Theorem (theorem:full-theorem-minus-uniqueness, 863): ExistenceHarmonicBallsStmt
- Proof: Sec 5.3, 951-1009.
  - Construction: Lemma 5.7 plus Prop 5.4 and a union bound give, for each k, the clusters Lambda^{B_k;kx}_t for t < A_k T^{(k)}.
    The family is defined piecewise in k (961-966); compatibility comes from Lemma 3.5 (968-970).
  - Unboundedness of the times, eq:strictly-increasing-times (974): T^{(k)} has the law of T^{(1)} (Lemma 5.7); reverse Fatou gives
    eq:positive-io (987); A_k -> infinity, eq:geometric-bm (991), via I3.
  - Uniqueness is deferred to Prop 5.6 (977).
- Consumed by: Thm 1.1 (870), Prop 5.6 statement (873), Lemma 5.8 (1024), Lemma 9.3 (2343), Prop 10.7 (2691), Lemma 11.6 (2782),
  Prop 11.2 (2943).
- Issues: G6 (four sub-points); G7.

### 5.6 Prop (prop:uniqueness, 872): UniquenessHarmonicBallsStmt
- Proof: Sec 9, 2415-2473, after Sak82 Thm 10.13 (inspiration only).
  - Lemma 9.4 (2417) reduces the claim to mu_h(A_{t0} \ Lambda-hat_{t0}) = 0.
  - Mass identities from Thm 5.5 and the hypotheses on A_t.
  - Monotonicity eq:cluster-monotonicity (2423): the A_t by hypothesis, Lambda-hat via Lemma 3.3 and Lemma 3.5.
  - Lemma 9.3 (2426); induction on times spaced by mu_h(B)/2.
  - I1 (mu_h(B) > 0).
- Consumed by: Thm 1.1 (871, 977).
- Issues: G8 (the step at 2432-2434; "origin" for z at 2422).

### 5.7 Lemma (lemma:scale-invariance-flow, 885): ClusterScaleInvarianceStmt
- Proof: 890-933. Pathwise identity Lambda^z_t[h'] = k^{-1} Lambda^{B_k;kz}_{A_k t}[h] with h' = h(k.) - h_k(0), and h' has the law of h
  (eq:h-coordinate-change).
- Uses: Lemma 3.1 (916); Fact 2.1 III (Weyl, with the random constant f = -h_k(0) - Q log k) and IV (dilation); G_{B_k}(kz,kx) = G_{B_1}(z,x); I4.
- Consumed by: Thm 5.5 proof (952, 980), Prop 10.7 (2690).
- Issues: G11; S1 (G_{B_{rk}(z)} at 922; "A_k^{-1} mu_h(k.)" at 918 means the pushforward under x -> x/k).

### 5.8 Lemma (lemma:strong-compatibility, 1019): ClusterStrongCompatibilityStmt
- Proof: 1023-1025, "immediate from the proof of Lemma 3.5 together with Theorem 5.5", using the extension to any bounded open U
  claimed at 1016-1017.
- Consumed by: Prop 1.3 (1037).
- Issues: G9; no "a.s." in the statement.

## Section 9

### 9.1 Lemma (lemma:obstacle-comp, 2285): ObstacleComparisonStmt
- Proof: 2295-2313. The proof is complete, so no External is needed: kind is "cited" in the inventory, but Lean can prove it.
  - (1): -G_{B_R}(.,x) is in the subharmonic test class (nu = -delta_x, O = B_R, which contains closure(A)); then use symmetry of G.
  - (2): G_{B_R}(.,x) for x in B_R \ A is in the class eq:harmonic-fns (nu = delta_x supported in O \ A). This needs the enlarged
    class when x is on the boundary of A.
- Lit: SS13b Thm 2.1; Sak84.
- Uses: D1, D5, Prop 2.3 (implicit), I4 (symmetry).
- Consumed by: Prop 9.2 (2321), Lemma 9.3 (2351, 2367).
- Issues: G13 ("strictly contained" lacks "in B_R" at 2286; the test function takes the value -infinity at x).

### 9.2 Prop (prop:sub-harmonic-ball-uniqueness, 2316): SubharmonicBallUniquenessStmt
- Proof: 2320-2324.
  - Lemma 9.1(1) and (2) (2321): for (2), a subharmonic ball satisfies equality for G_{B_R}(.,x), x not in A, by taking nu = +-delta_x.
  - f - t G_{B_R}(z,.) lies in S^{B_R;z}_t, using Prop 2.5 for continuity; minimality of lambda gives f >= v.
- Consumed by: none ("We do not use Proposition 9.2", 2327).
- Issues: F5 (the conclusion is stronger than what the proof shows); G15.

### 9.3 Lemma (lemma:contains-boundary, 2336): HarmonicBallBoundarySubsetStmt
- Proof: 2340-2383.
  - Enlarge R so that Lambda-hat_t(z) is compactly inside B_R; Thm 5.5 (2343) identifies Lambda-hat_t(z) with the regularised cluster
    in B_R, a subharmonic ball of mass t.
  - Auxiliary u, eq:auxiallary-function (2345). Step 1: u >= 0, by Lemma 9.1(2) for A, Lemma 9.1(1) for Lambda-hat, and the minimum principle on A.
  - Step 2: u = 0 off both sets, by Lemma 9.1(2) for both. Step 3: the strong minimum principle and I1.
- Uses: Lemma 9.1, Thm 5.5, Prop 2.5 (continuity of u, implicit), I1, I4.
- Consumed by: Prop 5.6 (2426).
- Issues: none beyond F1. Under the corrected test class, A is compactly inside B_R, so O = B_R is admissible.

### 9.4 Lemma (lemma:regular-open-ae, 2394): RegularOpenEqOfAEEqStmt
- Proof: 2399-2409, a topological argument plus I1. Only the regularity of Y is needed to get X \ Y empty.
- Consumed by: Prop 5.6 (2417).
- Issues: none. This is pure measure topology: a deterministic lemma for any measure of full support.

## Appendix A (deterministic: a Radon measure mu with eq:volume-growth)

Properties of q_{B_R} (3537-3541):
1. Hoelder: "same argument as Prop 2.5".
2. Delta q = -mu: AG01 Thm 4.3.8.
3. Zero boundary values: from G = 0 on the boundary.
4. Positivity: strong maximum principle.

### A.1 Lemma (lemma:appendix-basic-properties, 3589): ObstacleLeastSuperharmonicMajorantStmt
- Proof: 3593-3648. Work with f_t, eq:lsc-leastsuperharmonic (3594), with lsc competitors.
  - Step 1, finiteness: the minimum principle and q admissible.
  - Step 2: AG01 Thm 3.7.5.
  - Step 3, continuity: Poisson modification on B_delta(x0) and the super-mean-value property.
- Consumed by: Lemma 3.1 (3588), Lemma A.2 (3666); implicitly Lemmas A.3 and A.6.
- Issues: G2 (Step 3 fails at x0 = 0, where beta_t = -infinity).

### A.2 Lemma (lemma:appendix-non-coincedence-open-harmonic, 3652): ObstacleNonCoincidenceHarmonicStmt
- Proof: 3656-3725.
  - Step 1, open: continuity.
  - Step 2, harmonic: AG01 Thm 3.2.2, lowering by min(H, s~), eq:smaller to eq:above-obstacle (3674-3712).
  - Step 3, connected: the odometer is subharmonic on a component that misses 0 and vanishes on its boundary. Uses Lemma A.4
    implicitly, for the part of the boundary on the circle.
- Consumed by: Lemma 3.2 (3651), Lemma A.5 (3795).
- Issues: G1 (it proves only Delta s~ = 0 on Lambda; the nu-decomposition used later does not follow).

### A.3 Lemma (lemma:appendix-monotonicity, 3731): ObstacleMonotoneStmt
- Proof: 3734-3765. s~ := s~_{t2} + (t2 - t1) G(0,.) is a competitor for t1.
- Consumed by: Lemma 3.3 (3730).
- Issues: minor gap. s~ has a +infinity pole at 0, so it is not in S~_{t1} (a subset of the continuous functions on the closed disc),
  contrary to 3763. It is admissible in eq:lsc-leastsuperharmonic, and f_t = s~_t by Lemma A.1, so the argument survives.

### A.4 Lemma (lemma:appendix-zero-boundary, 3772): ObstacleOdometerZeroBoundaryStmt
- Proof: 3776-3784 (the line that carries the argument is 3777). On the circle, s~ is squeezed between beta_t = 0 and q = 0.
- Consumed by: Lemma A.5 (3795), Lemma 3.4; implicitly Lemmas A.2 and A.6.

### A.5 Lemma (lemma:appendix-conservation-of-mass, 3788): ObstacleConservationOfMassStmt
- Proof: 3792-3828.
  - eq:laplacian-of-v (3797-3803), including 0 <= nu <= mu (G1).
  - Weak normal derivative: Pon16 Prop 7.3, eq:weak-integration-by-parts (3806).
  - Sign of the normal derivative: Pon16 Lemma 12.15.
  - The normal derivative is classical and zero when closure(Lambda) is inside B_1.
- Consumed by: Lemma 3.4 (3769). The intermediate identity t = mu(Lambda) + nu(boundary Lambda) (3822-3825) is needed in the repair of Prop 4.1 (G3).
- Issues: G1 (mu(Lambda) <= t uses nu >= 0); S1 (mu_h for mu at 3790).

### A.6 Lemma (lemma:appendix-cluster-compatibility, 3851): ObstacleCompatibilityStmt
- Proof: 3856-3895.
  - eq:monotonicity-domains (3862): v^{B_{r1}} <= v^{B_{r2}}, via the competitor w-hat. G_{r1}(0,.) - G_{r2}(0,.) is constant, so w-hat is continuous.
  - Reverse inequality: v^{B_R} - v^{B_{s1}} is subharmonic on Lambda^{B_R} (uses nu <= mu only) and <= 0 on its boundary.
- Uses: eq:laplacian-of-v-general (3840), Prop 2.3 (Delta G = -delta), the maximum principle.
- Consumed by: Lemma 3.5 (3832), Lemma 5.8 (by extension).
- Issues: none of substance. The off-centre version (z instead of 0) is "verbatim".

## Issues

### F: printed statement false or not established as printed

- **F1. Test class of Thm 1.1, 139-146 ("for some O with Lambda(z) subset closure(O)").** The class admits an O with a slit inside Lambda.
  Take O = B_R \ S with S a closed segment in Lambda \ {z}, y in O \ closure(Lambda), and f2 = G_O(.,y), which lies in the
  class H~_O(Lambda).
  - The odometer identity t G(z,.) - G mu|_Lambda = v (Lemma 4.3) gives t f2(z) - int_Lambda f2 dmu_h = int_S v dsigma, where
    sigma = -Delta f2|_S <= 0 is non-zero (f2 > 0 on O and f2 = 0 on S). Also v > 0 on Lambda.
  - So the quantity is < 0: the mean-value property fails. With the literal class no cluster is a harmonic ball, and existence in
    Thm 1.1 is false. The same holds already for Lebesgue measure and a disc.
  - The remark at 753-754 ("the same as eq:sub-harmonic-potential with nu|_Lambda = 0") is also false for such O.
  - Fix: require closure(Lambda(z)) subset O, as at 749 ("O ... containing a neighborhood of the closure"), and nu of compact support
    in O. Sec 9 only uses O = B_R with A compactly inside B_R (2302-2309, 2351), so uniqueness survives.
- **F2. Lemma 2.4 exponent range (498).** Exact scaling (Fact 2.1 III-IV, eq:h-coordinate-change) gives
  mu_h(B_eps(0)) = eps^{gamma(Q-alpha0)} e^{gamma h^C_eps(0)} mu_{h~}(B_1), with h~ of the law of h and h^C_eps(0) ~ N(0, log 1/eps).
  - So log mu_h(B_eps(0)) / log eps -> gamma(Q-alpha0) in probability.
  - Since gamma(Q-alpha0) < (2-gamma)^2/2 iff alpha0 > 2, and gamma(Q-alpha0) > (2+gamma)^2/2 iff alpha0 < -2, the upper bound
    (resp. lower bound) of eq:ball-volume fails at z=0 with probability -> 1 for every beta+ in (gamma(Q-alpha0), (2-gamma)^2/2)
    when alpha0 > 2 (resp. every beta- in ((2+gamma)^2/2, gamma(Q-alpha0)) when alpha0 < -2).
  - The Oct-15 pointer proposes beta+ < min{(2-gamma)^2/2, gamma(Q-alpha0)} and beta- > max{(2+gamma)^2/2, gamma(Q-alpha0)}.
    That is consistent at z=0, but uniformity near 0 is not re-derived here.
  - Every downstream beta± inherits the change: Lemma 4.2, Sec 6, Prop 7.2 (2027) and App A.
- **F3. Lemma 4.2, "alpha = alpha(gamma)" (717, 722).** The exponent cannot be uniform in alpha0. Near 0, lambda is minus a potential
  of mu_h, and its oscillation on B_r(0) is at least about mu_h(B_{r/2}(0)), which is roughly r^{gamma(Q-alpha0)} by F2. So the Hoelder
  exponent is at most gamma(Q-alpha0), which tends to 0 as alpha0 rises to Q. This is a heuristic, not a full proof.
  Fix: alpha = alpha(gamma, alpha0) > 0.
- **F4. Prop 5.4 (853-856).** "for all r > 0" binds nothing, and T is unbound.
  - If T is the uniform T of Prop 5.1, the statement makes the exit time inf{t : closure(Lambda^z_t) meets the boundary of B_1} equal
    to T for every z in B_{1/2}. That is false in the deterministic analogue (Lebesgue measure: the exit time is pi(1-|z|)^2) and is
    not proved for mu_h.
  - If T = T(z), the statement is fine, but the proof of Thm 5.5 (952-958) uses a T^{(k)} uniform over centres. See G6.
- **F5. Prop 9.2 (2317).** The proof (2320-2323) gives only Lambda^{B_R;z}_t subset A, not int(closure(Lambda^{B_R;z}_t)) subset A.
  - With A = Lambda^{B_R;z}_t itself (a subharmonic ball by Lemma 4.3 when it is compactly inside B_R and mu_h(boundary)=0), the
    printed claim forces Lambda = int(closure Lambda), which the paper never proves.
  - Fix: conclude Lambda^{B_R;z}_t subset A, or assume A = int(closure A). The result is unused (2327).

### G: proof gaps (statement plausibly true)

- **G1 (central).** nu >= 0 in Lemma 3.2 (630-633), eq:laplacian-of-v (3797-3803) and eq:laplacian-of-v-general (3840-3846).
  - Lemmas A.1 and A.2 give only Delta s~ <= 0 on B_1 and Delta s~ = 0 on Lambda. Hence nu = (Delta s~ + mu)|_{boundary Lambda} <= mu.
  - nu >= 0 is the Lewy-Stampacchia bound Delta s~ >= -mu on B_1 \ {0}. Neither it nor the inverse maximum principle is cited (I5),
    and "this together with Lemma A.1 implies Lemma 3.2" (3650-3651) skips it.
  - It is used for mu(Lambda) <= t (3821, 3827) and for |density| <= 1 in Lemma 4.2.
  - Missing ingredient, to be supplied as a paper-owned proof or a proposed External: for a continuous obstacle psi with
    Delta psi = t delta_0 - mu, the least superharmonic majorant s~ satisfies -mu <= Delta s~ on B_1 \ {0}.
- **G2. Lemma A.1 Step 3 (3626-3628).** "beta_t(x) + eps/2 >= beta_t(y) for all x,y in B_delta(x0)" is false at x0 = 0, where
  beta_t(0) = -infinity. Fix: on B_delta(0), beta_t <= sup q + (t/2pi) log delta < 0 <= f_t (Step 1), so the Poisson
  modification stays admissible.
- **G3. Prop 4.1, last claim (711-712).** Lemma 3.4's equality case requires mu_h(boundary Lambda) = 0, which is not available. Fix:
  if closure(Lambda) is inside B_1, the identity from the proof of A.5 (3822-3825) gives t = mu_h(Lambda) + nu(boundary Lambda), so
  t <= mu_h(closure Lambda) < mu_h(B_1) by I1. Hence t >= t^+ = mu_h(B_1) forces closure(Lambda) to meet the boundary of B_1.
- **G4. Lemma 4.2 (730-733).** A constant C uniform in t and z needs a quantitative Prop 2.5: Hoelder seminorm <= C(h) ||f||_infty.
- **G5. Lemma 4.3 proof (781-786).** The proof replaces int_O G_O(.,x) dnu(x) by an integral over Lambda.
  - For nu charging O \ Lambda one needs t G_O(z,.) - int_Lambda G_O(y,.) mu_h(dy) = v on all of O (v extended by 0). Both sides have
    Laplacian -t delta_z + mu_h|_Lambda and vanish on the boundary of O, since closure(Lambda) is inside O.
  - Then int v dnu <= 0 because v = 0 off Lambda.
  - "v(z) dnu(x)" at 785 should be v(x); "Delta q(z)" at 776 should be Delta q(x).
- **G6. Thm 5.5 proof.**
  - (a) k0 = 3|z| (960) need not be an integer, and is 0 for z = 0. Take k0 = ceil(3|z|) + 1.
  - (b) "compactly embedded in closure(B_{k/2})" (957) is unjustified; scaling Prop 5.1 gives B_k.
  - (c) "the times A_k T^{(k)} are increasing in k" (968) and "using that T^{(k)} is increasing in k" (1004-1005) are unjustified:
    T^{(k)} is a lower bound uniform over centres, built from the rescaled field. Fix: use the exit times
    tau_k(z) = sup{t : closure(Lambda^{B_k;z}_t) subset B_k}. These are non-decreasing in k by Lemma 3.5, and tau_k(z) >= A_k T^{(k)}
    for z in B_{k/2}. Then limsup_k A_k T^{(k)} = infinity a.s. (from eq:positive-io and A_k -> infinity) is enough.
  - (d) The drift of the geometric BM (1003) omits alpha0: A_{e^t} = exp(gamma((Q - alpha0) t + B_t)). A_k -> infinity still holds since alpha0 < Q.
- **G7. Thm 1.1(b), "increase continuously in t (in the Hausdorff topology)" (157).** Props 5.2 and 7.2 give right-continuity only.
  Left-continuity is never stated. Short repair: if x is in Lambda_t but not in closure(union_{s<t} Lambda_s), a small ball around x
  has positive mass (I1) and misses that union, contradicting mu_h(Lambda_t) = t = lim mu_h(Lambda_s).
- **G8. Prop 5.6 proof (2432-2434).** "As the family {A_t} continuously decreases to {z}": hypothesis (b) only gives
  cap_t A_t = {z} for open sets, which does not yield B subset complement of A_{s0}. Fix:
  - The boundary of A_s lies in closure(Lambda-hat_s(z)) (Lemma 9.3), which is inside B_delta(z) for small s (Prop 5.2 scaled, or Thm 5.5).
  - The complement of closure(B_delta(z)) is connected and A_s is bounded, so A_s is inside closure(B_delta(z)).
- **G9. Lemma 5.8 (1016-1025).** "extend essentially verbatim to ... any bounded open set": for irregular U, G_U and q_U need not be
  continuous up to the boundary, and the class S^U (continuous functions on closure U) and the Appendix boundary arguments (A.4,
  A.5) use the ball. Fix: state Lemma 5.8 for smooth (or regular) bounded U. Prop 1.3 then follows by exhausting U with smooth U_n.
- **G10. Prop 2.5 and App A instantiation.** "Finiteness follows immediately from Lemma 2.4" (534), and "this follows from Lemma 2.4 and
  the scaling properties" (3529-3530). Both need I2: an a.s., all-scales, all-centres version on closure(O) or B_R, obtained by
  Borel-Cantelli over dyadic scales and eq:h-coordinate-change. Not written.
- **G11. Lemma 5.7.** "The laws of the families coincide" needs a measurable structure on families of sets (e.g. Hausdorff metric on
  closures, or the families as functions of h). The pathwise identity is what is actually used.
- **G12. Prop 5.2 scope.** It is stated for every t > 0, but the cited Prop 7.2 (2104) needs Lambda^z_t compactly inside B_1. For later t
  (after the cluster touches the boundary of B_1) continuity is unproved. Only t < T is used downstream.
- **G13. Lemma 9.1 (2286).** "a domain strictly contained" lacks "in B_R". The subharmonic test function -G_{B_R}(.,x) takes the value
  -infinity, whereas eq:sub-harmonic-potential asks for real values (746).
- **G15. Prop 9.2 proof (2323).** mu_h(Lambda-hat^{B_R;z}_t) = t needs Prop 8.1 scaled to B_R and Lemma 3.4. Neither is cited.

### S: slips and typos (fix in the Lean statements)

- 156: mu_h(boundary Lambda_t(x)) should be Lambda_t(z).
- 180: "t >= 0" should be t > 0.
- 448: "z in C" should be z in the complex plane.
- 547: dy should be mu_h|_K(dy).
- 597: eq:limit-odometer: t G_{B_r;z}(0,.) should be t G_{B_r}(z,.).
- 645: Lemma 3.3 drops ";z".
- 651 (Lemma 3.4): mu should be mu_h.
- 704-708: t log|x-z| should be -t G_{B_1}(z,x).
- 832 (Prop 5.2) and 2025 (Prop 7.2): "+ B_eps(z)" and "+ B_delta(z)" should be + B_eps and + B_delta.
- 837 (Prop 5.3): B_r(z) should be B_1.
- 854 (Prop 5.4): free "r > 0".
- 922: G_{B_{rk}(z)} should be G_{B_k}.
- 2422: "origin" should be z.
- 3527: upper exponent beta- should be beta+.
- 3790 (Lemma A.5): mu_h should be mu.
