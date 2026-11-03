# E19 route (b): the paper's chain without Liouville Brownian motion

Task e19-route-b (c2). Operator decision E19 (inbox, 2026-11-03): try route (b) first, i.e. keep the paper's chain verified
without Liouville Brownian motion (LBM). Report before attempting route (a). Line numbers refer to
paper/lqg_harmonic_ball-corrected.tex (no corrections applied in this region, so they coincide with the preserved source).

## Verdict

| Consumer (tex line) | Uses | Replaceable without LBM? | Reason |
|---|---|---|---|
| Prop 4.1 proof (693-710) | Prop 2.5: `q_1` finite | YES (already Green form) | `q_1` is *defined* by `Δq_1 = -μ_h` in `B_1`, `q_1 = 0` on `∂B_1` (694-698), i.e. `q_1 = ∫G_{B_1}(·,y)μ_h(dy)` (E7: the LBM exit time is `2q_1`). Only finiteness is used. |
| Lemma 4.2 proof (732) | Prop 2.5, Green clause | YES (already Green form) | Green potential of `ν ≪ μ_h`; no LBM. (G4 is separate: a quantitative bound and a bounded density are needed.) |
| Sec 6 text (1138) | Prop 2.5: `SG_ρ(x_0)` finite | YES (already Green form) | `SG` (1134) is a supremum of Green potentials of `μ_h|_{A}`. Positivity comes from I1, not Prop 2.5. |
| Lemma 6.7 proof (GRAPH 520) | `SG_1(0) ∈ (0,∞)` | YES | Same as 1138. |
| App A property 1 (3543) | "same argument as Prop 2.5" | YES | Green potential `q_{B_R}` (3533); no LBM. |
| Lemmas 4.3, 9.2, 9.3 (implicit) | bounded / continuous Green potentials | YES | Green clause only. |
| Lemma 6.4 proof, Step 2 (1219-1255) | Prop 2.6 (1234), GRV16 Prop 2.19 (1225), I6 | YES, by a new proof (§1.3) | The heat kernel is used only to make "small `μ_h` mass ⇒ small probability" uniform in `u ∈ ∂B_4`. §1.3 proves Step 2 from Green potentials (Prop 2.5, Green clause, on annuli inside `B_1`), I1, Fact 2.1 III-IV, eq:gff-scaling and planar Brownian motion. It uses no heat kernel, no LBM and no Lemma 6.5. |

So route (b) succeeds. The LBM clause of Prop 2.5 has no consumer. Prop 2.6 has one consumer (Lemma 6.4), and route (b) removes it.
D11 (LBM) and I6 (LBM as a time change) then have no use in the chain. `HarmonicBalls/Proposed/LBM.lean` was not created, and no LBM
input is staged.

Recommended actions (for the lead; none of these files is c2's to edit in this task):
1. Prop 2.5: consume only its Green clause. Split `GreenPotentialLiouvilleHolderStmt` (Draft/Section2.lean:153) into a
   clock-free statement (the second conjunct, with no `F` and no `IsLQGClock` hypothesis) that all consumers use, plus the LBM clause,
   which stays drafted as printed but unconsumed and is marked [NCS1].
2. Prop 2.6: record as [NCS1] (text in §2). Leave it unconsumed.
3. Lemma 6.4: replace the proof of Step 2 by §1.3. This is a proof replacement, not a statement correction: the statement (with
   [C23] and the G19 fix to Step 1) is unchanged.
4. GRAPH L1: GRV16 "Section 9" (1226) is Subsection 2.9 (arXiv p. 27). It exists, but it is a remark without proof (§2.2).

## 0. Conventions

`G_O` is normalized as in Prop 2.3 (`-ΔG_O(x,·) = δ_x`, E7). `B` is standard planar Brownian motion, independent of `h`, with law `P_x`
when started at `x`. For open `U`, `τ_U = inf{t ≥ 0 : B_t ∉ U}`. For Borel `E`, `T_E = inf{t > 0 : B_t ∈ E}`. `A := A_{3,5}(0)`.
The good-annulus event follows [C23]: `E_r(z;a,b)` means that for every Borel `Y ⊆ A_{3r,5r}(z)` with `μ_h(Y) ≤ a μ_h(A_{3r,5r}(z))`,
`sup_{u ∈ ∂B_{4r}(z)} P_u[τ_A ≤ τ_Y | h] ≤ b`. Here `τ_A ≤ τ_Y` holds iff `B_t ∈ Y` for all `t < τ_A`.

## 1. Consumers

### 1.1 Prop 2.5 (524-537)
Prop 2.5 has two clauses: (i) the expected exit time of LBM from `O` is finite and Hölder; (ii) "more generally",
`q(x) = ∫_O G_O(x,y) f(y) μ_h(dy)` is finite and Hölder on `closure O` for `f ∈ L^∞`. The proof (533-537) proves (ii) only
(Lemma 2.4 plus Campanato; Pon16 §16.2). Clause (i) follows from (ii) only through the Revuz correspondence
`E_x[F(τ_O)] = 2∫G_O(x,y)μ_h(dy)`, which presupposes a PCAF `F` with Revuz measure `μ_h`, i.e. LBM.
All consumers (table above) use (ii). The phrase "expected exit time of LBM" at 689, 693 and 3530 (`eq:expected-exit-time`) is only a
name: each place immediately characterizes the function as the Green potential.

### 1.2 Prop 2.6 (554-561)
The only consumer is Lemma 6.4, line 1234 (GRAPH 2.6). Lemma 6.4 uses only the following:
- (H1) existence of `p^K_T(u,v)`, a density of the law of `𝓑^u_T` with respect to `μ_h` (1233; slip S1 at 547 says `dy`);
- (H2) at the single random time `T` of eq:annulus-hit-time: `p^K_T` is finite and continuous on `∂B_4 × closure B_5`. This gives
  eq:heat-kernel-max, and hence eq:heat-kernel-int: `sup_{u ∈ ∂B_4} P[𝓑^u_T ∈ Y | h] ≤ C(h) μ_h(Y)`.

Strict positivity, continuity in `t` and the on-diagonal estimates are not used. Step 2 also uses GRV16 Prop 2.19 (continuity in `u`
of the law of the stopped LBM, 1225) with an implicit Dini argument to get eq:annulus-hit-time, and I6 (exit order is preserved by the
time change). All of these are LBM statements.

### 1.3 Lemma 6.4 without LBM (replacement for Step 2, 1219-1255)
Step 1 (reduction to `α_0 = 0`, with the G19 fix `a := (C_1/C_2)a'`) and the first paragraph of Step 2 (1220-1221: `P[E_r(z)]` does
not depend on `(r,z)` when `α_0 = 0`) are kept. Use the invariance to work at `(r,z) = (1/10, 0)` instead of `(1,0)`. Then every annulus
below lies in `B_1`, and Prop 2.5 is used only for smooth `O ⊆ B_1`, where Lemma 2.4 applies (so G10 and I2 are not needed). For
readability we write `A = A_{3,5}`, `∂B_4`, `A' = A_{3.75,4.25}`; the true sets are these scaled by 1/10.

Fix `b, p ∈ (0,1)` and `α_0 = 0`.

**Hitting bound (deterministic in `h`).** Let `U ⊆ B_1` be a smooth bounded annulus and let `L ⊆ U` be compact. Set
`g_L := ∫_L G_U(·,y) μ_h(dy)` and `M := sup_U ∫_U G_U(·,y)μ_h(dy)`. Then for every `y ∈ U`:
`P_y[T_L < τ_U] ≥ g_L(y)/M`.
Proof. By Prop 2.5 (Green clause, `f = 1_L`), `g_L` is finite and continuous on `closure U`. It is 0 on `∂U` (because
`G_U(x,·) = 0` there) and at most `M`. It is harmonic on `U \ L` (a Green potential is harmonic off the support of its measure; AG01
Thm 4.3.8 gives `Δg_L = -μ_h|_L`). If `y ∈ L`, the bound is trivial for `T_L` with `t ≥ 0`. Otherwise optional stopping for a bounded
function that is harmonic on `U \ L` and continuous on its closure gives
`g_L(y) = E_y[g_L(B_{τ_{U\L}})] ≤ M·P_y[T_L < τ_U]`.

**(A) Fine support of `μ_h` has full Lebesgue measure.** Almost surely, for Lebesgue-a.e. `x`, every Borel `E` with
`μ_h(B_ε(x) \ E) = 0` for some `ε > 0` satisfies `P_x[T_E = 0] = 1`.
Proof. For `r > 0` let `U_r(x) := A_{r/8, r}(x)`, `q_{r,x} := ∫_{U_r(x)} G_{U_r(x)}(·,y)μ_h(dy)`, and
`R_r(x) := inf_{∂B_{r/4}(x)} q_{r,x} / sup_{U_r(x)} q_{r,x}`.
1. `R_r(x) > 0`. The numerator is the minimum over a compact circle of a continuous function (Prop 2.5) that is positive at each point
   (`G_{U_r(x)} > 0` on `U_r(x)`, and `μ_h(U_r(x)) > 0` by I1). The denominator is finite by Prop 2.5.
2. If `r < ε`: `P_x[T_E < τ_{B_r(x)}] ≥ R_r(x)`. Brownian motion from `x` reaches `∂B_{r/4}(x)` before `τ_{B_r(x)}`. Apply the strong
   Markov property there and the hitting bound with `U = U_r(x)` and compact `L ⊆ E ∩ U_r(x)`. Then let `L` increase: by inner
   regularity and `μ_h(U_r(x) \ E) = 0`, monotone convergence gives `g_L → q_{r,x}`, and Dini's theorem makes the convergence
   uniform on the circle.
3. `{T_E = 0} = ∩_r {T_E < τ_{B_r(x)}}` (paths are continuous and `τ_{B_r(x)} ↓ 0`). So
   `P_x[T_E = 0] ≥ limsup_n R_{7^{-n}}(x)`. If this is positive, then `P_x[T_E = 0] = 1` by Blumenthal's 0-1 law
   (`{T_E = 0} ∈ F_{0+}`).
4. Fix `x`. `R_r(x)` is a function of `μ_h|_{U_r(x)}` and is invariant under multiplying `μ_h` by a constant. By translation and scale
   invariance of `h` modulo constants (eq:gff-scaling), Weyl scaling (Fact 2.1 III), the coordinate change (Fact 2.1 IV) and
   `G_{x+rD}(x+ra, x+rb) = G_D(a,b)`, `R_r(x)` has the law of `R_1(0)` for all `r, x` (for `α_0 = 0`). Put
   `δ(c) := P[R_1(0) < c]`; then `δ(c) → 0` as `c ↓ 0` by item 1. By reverse Fatou,
   `P[R_{7^{-n}}(x) ≥ c for infinitely many n] ≥ 1 - δ(c)`. Letting `c ↓ 0`: a.s. `limsup_n R_{7^{-n}}(x) > 0`.
5. Fubini over `P ⊗ Leb`. This needs joint measurability of `(ω, x) ↦ limsup_n R_{7^{-n}}(x)`: the potentials are continuous, so
   the inf and sup reduce to countable ones. Items 2-3 then apply to every such `x` and every such `E` at once, because the lower
   bound `R_r(x)` does not depend on `E`. ∎

In LBM language, (A) says that the clock is positive at positive times when LBM starts from Lebesgue-a.e. point (cf. GRV16 Thm 2.7
item 3, which covers all points in its setting). Lebesgue-a.e. is enough here.

**(B) A random `a` for each `b`.** Almost surely, for every `b ∈ (0,1)` there is `j` with `E_1(0; 2^{-j}, b)`.
Proof. Fix `h` in the events of (A), I1 and Prop 2.5, so that `0 < μ_h(A) < ∞`. Suppose (B) fails for some `b`. Then for every `j`
there are a Borel `Y_j ⊆ A` with `μ_h(Y_j) ≤ 2^{-j} μ_h(A)` and a point `u_j ∈ ∂B_4` with `P_{u_j}[τ_A ≤ τ_{Y_j}] > b`.
- By inner regularity, choose compact `K_j ⊆ A \ Y_j` with `μ_h(A \ K_j) ≤ 2^{1-j} μ_h(A)`. Let
  `w_K(x) := P_x[B_t ∉ K for all t ∈ [0, τ_A)]`. Staying in `Y_j` until `τ_A` avoids `K_j`, so `w_{K_j}(u_j) > b`.
- Mean value inequality. For `ρ ≤ 1/4`, `B_ρ(u_j) ⊆ A`. Apply the strong Markov property at the exit time of `B_ρ(u_j)`, whose exit
  law is uniform on the circle, and integrate over `ρ` with weight `2πρ`. This gives `w_K(u) ≤ (16/π) ∫_{B_{1/4}(u)} w_K dx`. Hence
  `∫_{A'} w_{K_j} dx > πb/16` for every `j`.
- Let `L_m := ∩_{j ≥ m} K_j` (compact, increasing in `m`) and `E := ∪_m L_m`. Then `μ_h(A \ L_m) ≤ 2^{2-m} μ_h(A)`, so
  `μ_h(A \ E) = 0`. Since `L_m ⊆ K_j` for `j ≥ m`, `w_{L_m} ≥ w_{K_j}`, so `∫_{A'} w_{L_m} > πb/16` for every `m`.
- `w_{L_m} ↓ w_E` pointwise: the avoidance events decrease and their intersection is avoidance of `E`. By dominated convergence,
  `∫_{A'} w_E ≥ πb/16`.
- But for a.e. `x ∈ A'`, (A) applies with `ε = 1/4` (`B_{1/4}(x) ⊆ A`), so `P_x[T_E = 0] = 1`. Since `τ_A > 0`, this gives
  `w_E(x) = 0`, so `∫_{A'} w_E = 0`. Contradiction. ∎

**(C) A deterministic `a`.** `E_1(0;a,b)` decreases as `a` increases. By (B), `P[E_1(0; 2^{-j}, b)] ↑ 1`, so some `a = 2^{-j} ∈ (0,1)`
gives `P[E_1(0;a,b)] ≥ p`. This is the paper's last step (1252-1254) with the random `a` of (B).

**Ingredients.** Prop 2.5 (Green clause, `O ⊆ B_1` annuli, `f = 1_L`); I1; Fact 2.1 III-IV; eq:gff-scaling; AG01 Thm 4.3.8;
inner regularity of finite Borel measures on `ℂ`; reverse Fatou; Fubini. For planar BM: the strong Markov property, Blumenthal's 0-1
law, uniform exit law from discs, optional stopping for harmonic functions continuous up to the boundary, and measurability of
`T_E` for Borel `E` (début theorem).
Not used: LBM, its heat kernel, GRV16 Prop 2.19, Kig19, I6, Lemma 6.5.

**Obligations shared with the paper, not created by route (b).** Measurability of `E_r(z;a,b)` in `ω` (a supremum over all Borel `Y`;
the paper uses `P[E_r(z)]` at 1185 and 1254). Joint measurability in (A5).

**Lean availability (pointer only).** MarkovProcess has the Dynkin representation at exit times for Feller semigroups with zero
generator (Trajectory/HarmonicRepresentation.lean:118) and exit times (Lifetime/ExitTime). A grep found no Blumenthal 0-1 law and no
named strong Markov theorem for planar BM.

## 2. "Not in the cited source" — text for [NCS1] (CORRECTIONS-PROPOSED.md:63)

**What the paper needs.**
- Prop 2.5, LBM clause: LBM for `h = h^ℂ - α_0 log|·|` (massless whole-plane GFF; `μ_h` from the circle-average regularization,
  Fact 2.1), killed on exiting a smooth bounded `O`, quenched (given `h`), for every start `x ∈ O`; the expected exit time is finite
  and Hölder in `x`.
- Prop 2.6: LBM for the same field, reflected in an arbitrary square `K` (in Lemma 6.4, side 100 centred at 0, so `K` contains the
  singularity), quenched, all starts. Its heat kernel with respect to `μ_h|_K` exists, is finite, jointly continuous and strictly
  positive on `(0,∞) × K × K`.

**[Ber15] Thm 1.2** (arXiv:1301.3356v1, p. 4; AIHP 51 (2015)). Setting (p. 3): `D` a domain, `h` the GFF with zero boundary values
(`H^1_0(D)`), circle averages `h_ε`, and Brownian motion with `Z_0 = z` for a fixed `z`. Quote: "Assume 0 ≤ γ < 2. Then
(Z_ε(t), t ≥ 0) converges almost surely as ε → 0 to a random process (Z(t), t ≥ 0) which is almost surely continuous up to the hitting
time of ∂D." This is annealed (a.s. for the joint law of `(h, B)`), for one fixed start, killed at `∂D`, zero-boundary field. It
says nothing about all starts, quenched laws, the whole-plane field, the log singularity, reflection, expected exit times or heat
kernels.

**[GRV16] Thm 2.7** (arXiv:1301.2876v4, pp. 10-11; AOP 44 (2016)). Field: the whole-plane *massive* GFF `X` (`m > 0`, covariance
`G_m`, p. 4), regularized by the `n`-regularized field `X_n` of the kernel decomposition (§2.1-2.2), with Liouville measure `M`.
Quote: "P_X-almost surely, there exists a unique PCAF denoted by F such that F(t) = F_R(t), for t < T_R. Furthermore, P_X-almost
surely: 1. the Revuz measure of F is M, [...] 3. for all x ∈ R², P^B_x-a.s., F is strictly increasing, [...] 5. the law of the pair
(B, F) [...] is a continuous function of x". This is quenched, for all starts, and a PCAF in the strict sense, but for the massive
field with the `X_n` cutoff. It does not cover the massless whole-plane GFF, the `-α_0 log|·|` singularity, the circle-average
measure, reflection, or heat kernels. **Prop 2.19** (p. 25), item 1: "the law in C(R+) of the LBM B under P^B_x is continuous with
respect to x", in the same setting. **§2.9** (p. 27), cited as "Section 9" at 1226: "Our method applies to other two-dimensional
manifolds like the torus, sphere, planar domains, . . . equipped with a log-correlated Gaussian field [...]". It gives no statement
and no proof for planar domains. Its only explicit change concerns `lim F(t) = ∞` on compact manifolds.

**[Kig19] Thm 13.1** (Mem. AMS 259 (2019). Checked against the 98-page preprint, p. 59; it restates Thm 1.1, preprint p. 5. Mem. AMS
page numbers not checked.) Quote: "Assume that α = 0. Let µ be a Borel regular probability measure on K. Suppose that there exist
positive constants c1, c2, α1, α2 such that α1 ≥ α2 and c1 r^{α1} ≤ µ(B∗(x, r)) ≤ c2 r^{α2} (13.1) for any x ∈ K and any r ∈ (0, 1].
Then µ has weak exponential decay, there exists a jointly continuous heat kernel pµ(t, x, y) on (0, ∞) × K × K associated with the
time change of the Brownian motion with respect to µ and [on-diagonal bounds (13.2)]". Here `K` is a generalized Sierpinski carpet with `α = 0` (i.e. `r_* = 1`, p. 46), which includes the unit
square `[0,1]²` of Thm 1.1; there the base process is reflected Brownian motion (preprint p. 2). "Time change" means the Hunt process of the
time-changed Dirichlet form `(E, F_µ)` on `L²(K, µ)` (§6, §10). It does not prove the following:
- Identification of this Dirichlet-form time change with the regularization-limit LBM of Ber15/GRV16 for the field `h`. Example 11.3
  (p. 47) only verifies weak exponential decay of "Liouville measure on [0,1]²", citing GRV16 Thm 2.2 and Andres-Kajino Lemma 3.1.
- Hypothesis (13.1) for `μ_h` on a square of side 100 that contains the singularity: it needs two-sided power bounds at every centre in
  `K` and every `r ≤ 1`. Lemma 2.4 gives them only for centres in `B_1` (G10/I2), with exponents [C1] at 0. Normalization to a
  probability measure, and the scaling from the unit square, are not in Kig19, though both are routine.
- Strict positivity: Thm 13.1 does not state it. Positivity appears in Thm 10.10 (p. 44) under "admissible and controlled by rate
  functions"; whether the proof of 13.1 (via Thms 12.14, 12.16) gives it was not checked.

The paper's "with input given by Lemma 2.4" (558) covers (13.1) only partly, and only after the scaling remark (559-560).
Correction to ESCALATIONS E19: Kig19 Thm 13.1 can be checked from the preprint (done above).

**Entry text proposed for [NCS1].** Prop 2.5, LBM clause, and Prop 2.6 are not in the cited sources in the scope the paper needs.
Ber15 Thm 1.2 is annealed, for one fixed start, with zero-boundary GFF and killing. GRV16 Thm 2.7 and Prop 2.19 are quenched and for
all starts, but for the massive whole-plane GFF with the `X_n` cutoff; their §2.9 is a remark without proof. Kig19 Thm 13.1 gives a
jointly continuous heat kernel for the Dirichlet-form time change of reflected BM on `[0,1]²` by a deterministic measure with
two-sided power volume bounds. It does not identify that process with LBM, does not state positivity, and does not cover the
log-singular field on a square of side 100 without I2. Neither clause is used in the verified chain: all consumers of Prop 2.5 use
its Green-potential clause, and Lemma 6.4 is proved without Prop 2.6 (docs/campaign/E19-route-b.md §1.3).
