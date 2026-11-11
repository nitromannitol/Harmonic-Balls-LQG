# Corrections to *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795)

Below are the corrections we have found in the printed version of the paper. Every one of them is already in our corrected
version of the manuscript. Result numbers are those of the paper. The substantive corrections come first, grouped by section:
they change a statement or replace a proof. The minor corrections (notation and references) follow at the end.

## Part 1. Substantive corrections

### Section 1: main results

**Theorem 1.1 (harmonic balls: test class)** <!-- C7 -->
- *Printed:* the test functions $f_2$ range over $\tilde H_O(\Lambda(z))$ for some open set $O$ with $\Lambda(z)\subset\overline O$.
- *Problem:* with this class, no bounded open set containing $z$ satisfies the defining identity, because a Green function of a suitable domain with a pole at a boundary point of $\Lambda(z)$ is admissible but violates it. Theorem 1.1 as printed is therefore false.
- *Correction:* $O$ is a bounded open set with $\overline{\Lambda(z)}\subset O$.

### Section 2: volume growth and heat kernel

**Lemma 2.4 (volume growth of $\mu_h$-balls)** <!-- C1 -->
- *Printed:* for each $\beta^+\in(0,(2-\gamma)^2/2)$ and $\beta^->(2+\gamma)^2/2$, the bounds $\varepsilon^{\beta^-}\le\mu_h(B_\varepsilon(z))\le\varepsilon^{\beta^+}$ hold for all $z\in B_1$, and similarly for annuli.
- *Problem:* at $z=0$, $\log\mu_h(B_\varepsilon(0))/\log\varepsilon\to\gamma(Q-\boldsymbol\alpha_0)$. The upper bound fails when $\boldsymbol\alpha_0>2$ and the lower bound fails when $\boldsymbol\alpha_0<-2$; both values are admissible, since $\boldsymbol\alpha_0\in(-\infty,Q)$.
- *Correction:* $\beta^+\in\bigl(0,\min\{(2-\gamma)^2/2,\gamma(Q-\boldsymbol\alpha_0)\}\bigr)$ and $\beta^->\max\{(2+\gamma)^2/2,\gamma(Q-\boldsymbol\alpha_0)\}$, in the statement and in both displays.

**Proposition 2.5 (heat kernel of the reflected LBM)** <!-- C5 -->
- *Printed:* $\mathbb P[\mathcal B^x_t\in dy\mid h]=p^K_t(x,y)\,dy$ (equation (2.13)).
- *Problem:* the heat kernel is a density with respect to $\mu_h$, the measure for which the process is reversible. The measure $\mu_h$ is singular with respect to Lebesgue measure, so Lebesgue measure is the wrong reference measure.
- *Correction:* $\mathbb P[\mathcal B^x_t\in dy\mid h]=p^K_t(x,y)\,\mu_h(dy)$.

### Section 3: clusters

**Equations (3.3) and (3.4) (cluster and odometer)** <!-- C3 -->
- *Printed:* the cluster and the odometer are defined with $G_{B_r;z}$, evaluated as $G_{B_r;z}(z,x)$ in (3.3) and as $G_{B_r;z}(0,\cdot)$ in (3.4).
- *Problem:* $G_{B_r;z}$ is not a defined object. The identity $\Delta u=-t\delta_z+\dots$ in Lemma 3.2 needs the Green function of $B_r$ with its pole at $z$.
- *Correction:* use $G_{B_r}(z,x)$ in (3.3) and $t\,G_{B_r}(z,\cdot)$ in (3.4).

**Lemma 3.3 (monotonicity of clusters)** <!-- C52 -->
- *Printed:* the statement omits the pole $z$ from both clusters and does not require $t>0$.
- *Problem:* the obstacle problem is defined only for $t>0$, and monotonicity compares clusters with the same centre.
- *Correction:* on an event of probability one, for all $0<t_1\le t_2$, $r>0$ and $z\in B_r$, we have $\Lambda^{B_r;z}_{t_1}\subseteq\Lambda^{B_r;z}_{t_2}$.

**Lemma 3.5 (cluster compatibility)** <!-- C54 -->
- *Printed:* the mass parameter $t$ is free in the statement.
- *Problem:* the event on which compatibility holds must not depend on $t$, so $t$ has to be quantified inside it.
- *Correction:* for each $R>0$, on an event of probability one: for all $t>0$, $s_1\le R$ and $z\in B_{s_1}$, if $\overline{\Lambda^{B_{s_2};z}_t}\subset B_{s_1}$ for some $s_2\in[s_1,R]$, then $\Lambda^{B_s;z}_t=\Lambda^{B_{s_2};z}_t$ for all $s\in[s_1,R]$.

### Section 4: odometer

**Lemma 4.2 (Hölder continuity of the odometer)** <!-- C55 -->
- *Printed:* the deterministic Hölder exponent depends only on $\gamma$.
- *Problem:* the local power law near the origin depends on the log-singularity strength $\boldsymbol\alpha_0$, so the exponent must depend on it as well.
- *Correction:* the exponent may depend on $\gamma$ and $\boldsymbol\alpha_0$. The random constant stays uniform in $t,z,x,y$.

### Section 5: upper bounds and the global family

**Proposition 5.2 (continuity of clusters)** <!-- C56 -->
- *Printed:* the family is defined with the translated ball $B_\varepsilon(z)$, and its continuity at all times is justified only by Proposition 7.2, which assumes compact containment.
- *Problem:* that hypothesis is not available at all times.
- *Correction:* use the ordinary $\varepsilon$-neighbourhood, and state continuity only for the times before the cluster reaches the boundary of the unit ball, which is the scope the argument proves.

**Proposition 5.3 (boundary measure of clusters)** <!-- C57 -->
- *Printed:* the radius $r$ is unbounded, and the containment is in $B_r(z)$.
- *Problem:* $r$ is not bound by anything, and the containment is not the one used in Proposition 8.1.
- *Correction:* for $z\in B_1$ and $t>0$ with $\overline{\Lambda^{z}_t}\subset B_1$, we have $\mu_h(\partial\Lambda^{z}_t)=0$.

**Proposition 5.4 (regularised clusters)** <!-- C58 -->
- *Printed:* there is an unused universal $r$, an unbounded $T$, and a "strict containment" in the closed unit ball.
- *Problem:* $T$ must depend on the centre and on the sample, and the containment must be compact in the open ball.
- *Correction:* for every $z\in B_{1/2}$ there is a positive random $T=T(z)$ such that $\widehat\Lambda^{z}_t\Subset B_1$ for all $0<t<T$.

**Theorem 5.5 (proof)** <!-- C59 -->
- *Printed:* the proof uses an equality in law for a fixed centre and a union bound over all centres; it uses centre-independent exit times; and it does not prove overlap gluing or two-sided Hausdorff continuity.
- *Problem:* the union bound over centres does not follow from the fixed-centre statement, and the gluing and continuity claims are not proved.
- *Correction:* rewrite the proof with the pathwise dyadic covariance (as in the correction of Proposition 10.7 below), canonical exit times, compatibility of the clusters, and local-to-global continuity. The all-centre event and the two-sided continuity are stated explicitly.

**Lemma 5.8 (strong compatibility)** <!-- C60 -->
- *Printed:* $z$ may lie outside $U$, and an "essentially verbatim" extension is asserted for an arbitrary bounded open set $U$.
- *Problem:* the boundary continuity of the Green function can fail at irregular points.
- *Correction:* $U$ is a deterministic bounded Green-regular open set containing the pole. The statement of Proposition 1.3 is kept for every deterministic open $U$; the auxiliary lemma is restricted to Green-regular domains, and the locality proof passes through a smooth exhaustion by such domains.

### Section 6: annuli and odometer comparison

**Proposition 6.2 (good annuli) and the proof of Lemma 6.4** <!-- C23 -->
- *Printed:* the good-annulus event asks that "$\mathcal B^u$ exits $\mathcal A_{3r,5r}(z)$ before exiting $Y$", for Borel sets $Y\subset\mathcal A_{3r,5r}(z)$; the proof of Lemma 6.4 uses the same wording.
- *Problem:* when $Y\subset\mathcal A_{3r,5r}(z)$, the strict event is empty, so the condition does not express what is intended.
- *Correction:* "exits $\mathcal A_{3r,5r}(z)$ no later than exiting $Y$", that is, the exit time of the annulus is at most the exit time of $Y$.

**Lemma 6.4 (annuli are hit)** <!-- C61 -->
- *Printed:* $a=a(b,p,\gamma)$, and the constants in the proof depend only on $\gamma$.
- *Problem:* the comparison with the log-singular field depends on $\boldsymbol\alpha_0$.
- *Correction:* $a=a(b,p,\gamma,\boldsymbol\alpha_0)$, and the constants in the proof depend on $\boldsymbol\alpha_0$ as well.

**Lemma 6.7 (very good annuli are hit)** <!-- C62 -->
- *Printed:* the dependence of $a$, $C^{\pm}_i$ and $N_1$ on $\boldsymbol\alpha_0$ and on the lower volume exponent $\beta^-$ is suppressed.
- *Problem:* the comparison with the singular field uses these dependencies, so they cannot be suppressed.
- *Correction:* $a=a(b,p,\gamma,\boldsymbol\alpha_0,\beta^-)$, the constants $C^{\pm}_1,C^{\pm}_2$ depend on $a,\gamma,p,\boldsymbol\alpha_0,\beta^-$, and $C_3>0$ is universal. The dependence of $N_1$ is displayed in the proof.

**Lemma 6.9 (harmonic odometer comparison)** <!-- C63 -->
- *Printed:* the comparison allows an infinite boundary supremum to be multiplied by a zero exit probability.
- *Problem:* the product $\infty\cdot 0$ is not controlled by the argument.
- *Correction:* add the premise $\sup_{\partial A\cap\overline{\Lambda^x_t}}v^{z}_t<\infty$. Every later application satisfies it.

**Lemma 6.13 (small odometer from low mass)** <!-- C64 -->
- *Printed:* the hypothesis is only that the annulus does not contain $z$.
- *Problem:* the component and odometer argument uses the whole closed ball, which must stay in $B_1$ and away from the pole.
- *Correction:* assume $\overline B_\rho(x_0)\subset B_1\setminus\{z\}$.

### Section 7: continuity of clusters

**Proposition 7.2 (continuity of clusters)** <!-- C18 -->
- *Printed:* $\Lambda_{t+\varepsilon}(z)\Subset\Lambda_t(z)+B_\delta(z)$, with $\delta=C\varepsilon^{1/(4\beta^-)}$.
- *Problem:* the ball $B_\delta(z)$ is centred at $z$. For $z\neq0$ and small $t$ the cluster lies in $B_{|z|/2}(z)$, so every $\lambda\in\Lambda_t(z)$ has $|\lambda|>\delta$ and $z\notin\Lambda_t(z)+B_\delta(z)$, although $z\in\Lambda_{t+\varepsilon}(z)$.
- *Correction:* $\Lambda_t(z)+B_\delta$, the ordinary $\delta$-neighbourhood, as in Proposition 5.2.

### Section 9: sub-harmonic balls

**Section 9.2, introduction to Lemma 9.3 (harmonic balls)** <!-- C22 -->
- *Printed:* every harmonic ball "in the sense of eq:harmonic-ball" has boundary in the closure of a regularised cluster.
- *Problem:* the printed class of test functions is too narrow. Under it, sets such as $B_1\setminus[1/2,3/4]$, or $\{x\in B_1:|x|\notin C\}$ with $C$ a fat Cantor set, satisfy the defining identity, while Lemma 9.1(2) and Lemma 9.3 fail for them.
- *Correction:* "in the sense of Theorem 1.1", the class enlarged as in the correction of Theorem 1.1.

**Proposition 9.2 (uniqueness of sub-harmonic balls)** <!-- C51 -->
- *Printed:* the inclusion $\widehat\Lambda\subset A$ for the sub-harmonic ball $A$ of mass $t$.
- *Problem:* at the last time a bounded hole disappears, the cluster is a sub-harmonic ball that omits a nonempty set inside its regularisation, so the inclusion fails.
- *Correction:* $\Lambda^{B_R;z}_t\subset A\subset\widehat\Lambda^{B_R;z}_t$, with $\mu_h(A\setminus\Lambda^{B_R;z}_t)=\mu_h(\widehat\Lambda^{B_R;z}_t\setminus A)=0$, and $A=\widehat\Lambda^{B_R;z}_t$ when $A$ is a regular open set. The paper does not use this proposition.

### Section 10: crossings and complementary components

**Lemma 10.5 (crossing components)** <!-- C48 -->
- *Printed:* every crossing component of $U^c\cap A$ contains a crossing component of the cluster.
- *Problem:* this is false, because clusters can have holes: a crossing component can be a whole annulus inside another hole.
- *Correction:* a deterministic statement. Finitely many crossings at small scales give local connectedness, no cut points, and simple-loop boundaries for the complementary components (Torhorst's theorem; see Jolivet, Loridant and Luo, arXiv:1411.6776, Theorem 3.1).

**Proposition 10.6 (complementary components of clusters)** <!-- C49 -->
- *Printed:* the components of $B_1\setminus\overline{\Lambda^z_t}$.
- *Problem:* the outer component of $B_1\setminus\overline{\Lambda^z_t}$ has a disconnected frontier.
- *Correction:* the components of $\mathbb C\setminus\overline{\Lambda^z_t}$, for clusters with $\Lambda^z_t\Subset B_1$. The proof uses Lemma 10.1 and the corrected Lemma 10.5.

**Proposition 10.7 (boundary of full clusters)** <!-- C50 -->
- *Printed proof:* a combination of Lemma 5.7, Lemma 10.1, a union bound and Theorem 5.5.
- *Problem:* Lemma 5.7 is an equality in law for a fixed centre, and a union bound over uncountably many centres is not available.
- *Correction:* the statement is unchanged. The proof uses a pathwise dyadic rescaling of Proposition 10.6, a countable intersection, and the closure identity of Theorem 5.5.

### Section 11: metric balls and the pinch event

**Lemma 11.5 (no exterior cone condition)** <!-- C40 -->
- *Printed:* each cone is contained in a rational cone.
- *Problem:* sector mass is monotone under inclusion, so the containing rational cone does not give the required inequality.
- *Correction:* each nondegenerate cone contains a smaller cone with rational extremal directions. Its sector mass is no larger, so its good scales are also good for the original cone.

**Lemma 11.5 (no exterior cone condition), good-event inequality** <!-- C41 -->
- *Printed:* the good-event inequality uses the annulus $\mathcal A_{3r,5r}(z)$.
- *Problem:* the event controls the mass in $\mathcal A_{r,2r}(z)$, not in $\mathcal A_{3r,5r}(z)$.
- *Correction:* replace $\mathcal A_{3r,5r}(z)$ by $\mathcal A_{r,2r}(z)$, so that $\mu_h(\mathcal A_{r,2r}(z)\cap\mathcal Q(z))\ge M\cdot SG_{3r,6r}(z)>C\cdot SG_{3r,6r}(z)$.

**Lemma 11.7 (bad scales and Harnack)** <!-- C39 -->
- *Printed:* the separated-annulus probability bound is applied directly at the origin and transferred.
- *Problem:* the separated-annulus bound alone does not give the positive rooted frequency required.
- *Correction:* the positive rooted frequency at $\alpha=\gamma$ is established by dilation ergodicity, and transferred by the rooted-field identity.

**Lemma 11.8 (bump construction)** <!-- C37 -->
- *Printed:* the bump height $\log(MC_2/C_1)/\gamma$ is nonnegative, and the drift comparison has a universal constant.
- *Problem:* the height can be negative, and the weight comparison depends on $\boldsymbol\alpha_0$.
- *Correction:* use a nonnegative bump of height $\log\max\{1,2MC_2/C_1\}/\gamma$, and the comparison factor $1201^{-\gamma|\boldsymbol\alpha_0|}$.

**Pinch-event geometry (before Lemma 11.12)** <!-- C42 -->
- *Printed:* the figure specifies $U\subset T$ and $Q'\subset Q$, without quantitative buffers.
- *Problem:* the locality, bump-support and path-connection arguments require explicit separations.
- *Correction:* a buffered keyhole geometry with explicit buffers and the connected component $\Omega$, specified in the text.

**Lemma 11.12 (pinch positive probability)** <!-- C43 -->
- *Printed:* the statement is for $\alpha_0=0$ and $P[\tilde G_1(0)]>0$.
- *Problem:* the tilde denotes a different event, and the rooted transfer needs $\alpha=\gamma$.
- *Correction:* for every $\alpha<Q$ and every $M>0$, $P[\widehat G_1^{h^\alpha}(0;M)]>0$, proved with local certificates.

**Lemma 11.17 and its three-event proof** <!-- C44 -->
- *Printed:* the bump proof of the three events uses unbuffered supports and an incorrect shrinking factor. It also uses $\overline O_2\subset B_{4\delta}(W)\setminus\overline{B_\delta(U)}$, which fails on the outer circle $|x-c|=R+4\delta$ for concentric balls $U=B_u(c)$, $V=B_v(c)$, $W=B_R(c)$.
- *Problem:* the supports and the strict inequalities do not suffice, and the open ball $B_{4\delta}(W)$ does not contain $\overline O_2$.
- *Correction:* replace the bump proof by local certificates and a joint large-mass, small-diameter construction. The closure of $O_2$ lies in the closed $4\delta$-neighbourhood of $W$, which lies in $B_{5\delta}(W)$: $\overline O_2\subset\overline{B_{4\delta}(W)}\setminus\overline{B_\delta(U)}\subset B_{5\delta}(W)\setminus\overline{B_\delta(U)}$. The inner separation $(v-\delta)-(u+\delta)>8\delta$ is unchanged.

**Lemma 11.13 (many pinch scales)** <!-- C45 -->
- *Printed:* the proof uses positive probability at $\alpha=0$ directly for typical points, and transfers the frequency from the unrooted field; global metric events are treated as if they were annular-local.
- *Problem:* the rooted law has a logarithmic singularity, and global metric events are not annular-local.
- *Correction:* the proof uses dilation ergodicity, the certificate at $\alpha=\gamma$, and the rooted-field transfer. The statement is unchanged.

**Proposition 11.11 (clusters are not metric balls)** <!-- C46 -->
- *Printed:* the proof argues with a metric ball centred at $0$ and with a loose union over times.
- *Problem:* metric balls can have arbitrary centres, and the exceptional set of times is random.
- *Correction:* the proof treats arbitrary metric centres and proves the boundary-union identity through arrival times. The statement is as printed.

### Appendix A

**Standing volume-growth condition (Appendix A)** <!-- C65 -->
- *Printed:* both sides of the condition $r^{\beta^-}\le\mu(B_r(z))\le r^{\beta^+}$ use $\beta^-$.
- *Problem:* the upper bound must use $\beta^+$.
- *Correction:* $r^{\beta^-}\le\mu(B_r(z))\le r^{\beta^+}$ for all $z\in B_R$.

**Obstacle $\beta_t$ (Appendix A)** <!-- C66 -->
- *Printed:* $\beta_t:\overline{B_1}\to\mathbb R\cup\{+\infty\}$.
- *Problem:* $\beta_t(0)=-\infty$, so the codomain is wrong, and the majorization condition at the pole should be stated explicitly (it is vacuous there).
- *Correction:* $\beta_t:\overline{B_1}\to\mathbb R\cup\{-\infty\}$, with the majorization condition at the pole stated as vacuous.

**Lemma A.5 (conservation of mass for obstacle clusters)** <!-- C67 -->
- *Printed:* the equality conclusion uses the LQG-specific measure $\mu_h$.
- *Problem:* the appendix is written for an arbitrary Radon measure $\mu$.
- *Correction:* for the measure $\mu$ fixed in the appendix: $\mu(\Lambda_t)\le t$ for $t>0$, and if $\overline{\Lambda_t}\subset B_1$ and $\mu(\partial\Lambda_t)=0$, then $\mu(\Lambda_t)=t$.

**Lemma A.6 (compatibility for obstacle clusters)** <!-- C68 -->
- *Printed:* $t$ is free, $s_1$ may be nonpositive, and $s_2$ is not scoped as an arbitrary quantified radius.
- *Problem:* as printed, the statement is not well defined.
- *Correction:* for every $t>0$, every $0<s_1\le R$ and every $s_2\in[s_1,R]$: if $\overline{\Lambda_{B_{s_2}}(t)}\subset B_{s_1}$, then $\Lambda_{B_s}(t)=\Lambda_{B_{s_2}}(t)$ for all $s\in[s_1,R]$.

## Part 2. Minor corrections

### Section 1

**Theorem 1.1(a)** <!-- C6 -->
- *Printed:* $\mu_h(\partial\Lambda_t(x))=0$.
- *Correction:* $\mu_h(\partial\Lambda_t(z))=0$ (the variable $x$ is not bound).

### Section 3

**Lemma 3.4 (conservation of mass)** <!-- C53 -->
- *Printed:* the equality case assumes zero boundary mass for an undefined measure $\mu$.
- *Correction:* use $\mu_h$, the LQG measure used throughout Lemma 3.4.

### Section 11

**Definition 11.1 (Lipschitz domain)** <!-- C12 -->
- *Printed:* the local graph description uses $U\cap B_r(x_0)$, where $U$ is not defined in the definition.
- *Correction:* $A\cap B_r(x_0)$, the set being defined.

**Lemma 11.6 (comparison chain)** <!-- C38 -->
- *Printed:* the reference is to the fixed-aspect-ratio definition of the annular potential.
- *Correction:* refer to the variable-aspect-ratio definition, since the potential has variable aspect ratio.

### Notation

**Annular potential shorthands** <!-- C47 -->
- *Printed:* the shorthands $SG_{s_1\rho,s_2\rho}$ and $SG_{3r,6r}$ link to the fixed-aspect-ratio definition.
- *Correction:* link them to the variable-aspect-ratio definition.

## INTERNAL - NOT FOR THE EMAIL

Early items [C1]-[C36] that are not in the email above, one line each with the reason. Patches of the email items are in CORRECTIONS.md (applied in commit 4568f76f).

- [C2]: superseded by [C65] (the same Appendix A volume-growth correction; upper exponent beta+).
- [C4]: superseded by [C53] (Lemma 3.4, equality case) and [C67] (Lemma A.5).
- [C8]: superseded by [C55] (Lemma 4.2 exponent depends on gamma and alpha_0).
- [C9]: superseded by [C58] (Proposition 5.4: T = T(z), delete "for all r > 0").
- [C10]: superseded by [C51]; the weak form Lambda subset A is part of [C51]. Operator 04:35: the Stmt of Prop 9.2 stays as printed (PARTIAL), the weak form is proved separately; the printed conclusion is not shown false.
- [C11]: superseded by [C43] (Lemma 11.12 for every alpha < Q with the hat-G event; operator E13).
- [C13]: superseded by [C52] (Lemma 3.3).
- [C14]: superseded by [C54] (Lemma 3.5) and [C68] (Lemma A.6).
- [C15]: superseded by [C64] (Lemma 6.13).
- [C16]: superseded by [C49] (Proposition 10.6: components of C minus the closure).
- [C17]: not adopted (operator 04:35: proof gap only, no statement change).
- [C19]: superseded by [C57] (Proposition 5.3).
- [C20]: superseded by [C58] (Proposition 5.4 containment).
- [C21]: superseded by [C60] (Lemma 5.8: z in U).
- [C24]: superseded by [C63] (finite-supremum premise; the early text "z not in closure(A)" is an equivalent alternative).
- [C25]: superseded by [C61]. The early text names a(b,gamma); the counterexample (docs/campaign/cex/AlphaUniformity.md section 2) refutes Lemma 6.4, whose constant is a(b,p,gamma). Lemma 6.3 with a(b,gamma) is true (section 6.2 of the same file).
- [C26]: superseded by [C62] (AlphaUniformity.md section 5).
- [C27]-[C36]: UNCLEAR. No correction text, analysis or adoption exists for these tags in CORRECTIONS-PROPOSED.md, FROZEN.md, ESCALATIONS.md, GAPS-HB-1106.md or docs/campaign/cex/. The adopted early set is C1-C9, C11-C16, C18-C26 (C10 in weak form only).
