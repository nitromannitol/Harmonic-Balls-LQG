# Corrections to *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795)

Below are the corrections we have found in the printed version of the paper. Each correction in Parts 1 and 2 is marked in
our corrected version of the manuscript. Result numbers are those of the paper. The substantive corrections come first,
grouped by section: they change a statement or replace a proof. The minor corrections (notation, references and dependence
bookkeeping) follow. Part 3 lists gaps in printed proofs that are not statement changes.

## Part 1. Substantive corrections

### Section 1: main results

**Theorem 1.1 (harmonic balls: test class)** <!-- C7 -->
- *Printed:* the test functions $f_2$ range over $\tilde H_O(\Lambda(z))$ for some open set $O$ with $\Lambda(z)\subset\overline O$.
- *Problem:* with this class, the defining identity can fail. For example, let $O=B_R\setminus S$ with $S$ a slit through $z$, so that $z\in\partial O$. The failure comes from the slit through $z$, not from a pole on $\partial\Lambda(z)$: any pole in $O\setminus\Lambda(z)$ works. With $\overline{\Lambda(z)}\subset O$ the identity holds, which is why the correction is stated that way. Theorem 1.1 as printed is therefore false.
- *Correction:* $O$ is a bounded open set with $\overline{\Lambda(z)}\subset O$.

### Section 2: volume growth and heat kernel

**Lemma 2.4 (volume growth of $\mu_h$-balls)** <!-- C1 -->
- *Printed:* for each $\beta^+\in(0,(2-\gamma)^2/2)$ and $\beta^->(2+\gamma)^2/2$, the bounds $\varepsilon^{\beta^-}\le\mu_h(B_\varepsilon(z))\le\varepsilon^{\beta^+}$ hold for all $z\in B_1$, and similarly for annuli.
- *Problem:* at $z=0$, $\log\mu_h(B_\varepsilon(0))/\log\varepsilon\to\gamma(Q-\boldsymbol\alpha_0)$. The upper bound fails when $\boldsymbol\alpha_0>2$ and the lower bound fails when $\boldsymbol\alpha_0<-2$; both values are admissible, since $\boldsymbol\alpha_0\in(-\infty,Q)$.
- *Correction:* $\beta^+\in\bigl(0,\min\{(2-\gamma)^2/2,\gamma(Q-\boldsymbol\alpha_0)\}\bigr)$ and $\beta^->\max\{(2+\gamma)^2/2,\gamma(Q-\boldsymbol\alpha_0)\}$, in the statement.

**Equation (2.13) (heat kernel of the reflected LBM)** <!-- C5 -->
- *Printed:* $\mathbb P[\mathcal B^x_t\in dy\mid h]=p^K_t(x,y)\,dy$ (equation (2.13)).
- *Problem:* the heat kernel is a density with respect to $\mu_h$, the measure for which the process is reversible. The measure $\mu_h$ is singular with respect to Lebesgue measure, so Lebesgue measure is the wrong reference measure.
- *Correction:* $\mathbb P[\mathcal B^x_t\in dy\mid h]=p^K_t(x,y)\,\mu_h(dy)$.

### Section 3: clusters

**Equations (3.3) and (3.4) (cluster and odometer)** <!-- C3 -->
- *Printed:* the cluster and the odometer are defined with $G_{B_r;z}$, evaluated as $G_{B_r;z}(z,x)$ in (3.3) and as $G_{B_r;z}(0,\cdot)$ in (3.4).
- *Problem:* $G_{B_r;z}$ is not a defined object. The identity $\Delta u=-t\delta_z+\dots$ in Lemma 3.2 needs the Green function of $B_r$ with its pole at $z$.
- *Correction:* use $G_{B_r}(z,x)$ in (3.3) and $t\,G_{B_r}(z,\cdot)$ in (3.4).

### Section 5: upper bounds and the global family

**Proposition 5.2 (continuity of clusters)** <!-- C56 -->
- *Printed:* the family is defined with the translated ball $B_\varepsilon(z)$, and its continuity at all times is justified only by Proposition 7.2, which assumes compact containment.
- *Problem:* that hypothesis is not available at all times.
- *Correction:* use the ordinary $\varepsilon$-neighbourhood, and state continuity only for the times before the cluster reaches the boundary of the unit ball, which is the scope the argument proves.

**Proposition 5.3 (boundary measure of clusters)** <!-- C57 -->
- *Printed:* the radius $r$ is unbound, and the containment is in $B_r(z)$.
- *Problem:* $r$ is not bound by anything, and the containment is not the one used in Proposition 8.1.
- *Correction:* for $z\in B_1$ and $t>0$ with $\overline{\Lambda^{z}_t}\subset B_1$, we have $\mu_h(\partial\Lambda^{z}_t)=0$.

**Proposition 5.4 (regularised clusters)** <!-- C58 -->
- *Printed:* there is an unused universal $r$, an unbounded $T$, and a "strict containment" in the closed unit ball.
- *Problem:* $T$ must depend on the centre and on the sample, and the containment must be compact in the open ball. (The printed "unbounded $T$" should read "unbound $T$": no dependence on the centre or the sample is stated.)
- *Correction:* for every $z\in B_{1/2}$ there is a positive random $T=T(z)$ such that $\widehat\Lambda^{z}_t\Subset B_1$ for all $0<t<T$.

**Theorem 5.5 (proof)** <!-- C59 -->
- *Printed:* the proof uses an equality in law for a fixed centre and a union bound over all centres; it uses centre-independent exit times; and it does not prove overlap gluing or two-sided Hausdorff continuity.
- *Problem:* Lemma 5.7 is an equality in law for a fixed centre, and the printed proof does not justify passing from it to all centres; the gluing and continuity claims are not proved.
- *Correction:* rewrite the proof with the pathwise dyadic covariance (as in the correction of Proposition 10.7 below, which rests on Proposition 10.6), canonical exit times, compatibility of the clusters, and local-to-global continuity. The all-centre event is stated explicitly. Right-continuity in $t$ follows from Propositions 5.2 and 7.2. Two-sided continuity, as needed for Theorem 1.1(b), is not yet proved in the corrected draft: left-continuity is missing, and the proof must not cite Proposition 5.4 for it.

**Lemma 5.8 (strong compatibility)** <!-- C60 -->
- *Printed:* $z$ may lie outside $U$, and an "essentially verbatim" extension is asserted for an arbitrary bounded open set $U$.
- *Problem:* for $z\notin U$ the cluster is empty ($\Lambda=\emptyset$), so $z$ must lie in $U$; and the boundary continuity of the Green function can fail at irregular points.
- *Correction:* $U$ is a deterministic bounded Green-regular open set containing the pole. The statement of Proposition 1.3 is kept for every deterministic open $U$; the auxiliary lemma is restricted to Green-regular domains, and the locality proof passes through a smooth exhaustion by such domains.

### Section 6: annuli and odometer comparison

**Lemma 6.4 (annuli are hit)** <!-- C61 -->
- *Printed:* $a=a(b,p,\gamma)$, and the constants in the proof depend only on $\gamma$. The transfer from the comparison field to $h$ also uses the factor $|z|^{-\boldsymbol\alpha_0\gamma}$ and a ratio in the wrong direction.
- *Problem:* the comparison with the log-singular field depends on $\boldsymbol\alpha_0$. The factor $|z|^{-\boldsymbol\alpha_0\gamma}$ is not uniform on the annulus when $|z|$ is of order $r$ or $z=0$, and the transfer of the event uses the exact Weyl density, which gives the constant $a=a'/1001^{\gamma|\boldsymbol\alpha_0|}$.
- *Correction:* $a=a(b,p,\gamma,\boldsymbol\alpha_0)$, and the constants in the proof depend on $\boldsymbol\alpha_0$ as well. Replace the factor $|z|^{-\boldsymbol\alpha_0\gamma}$ by the sup/inf ratio of $|x|^{-\boldsymbol\alpha_0\gamma}$ over the annulus, which is at most $1001^{\gamma|\boldsymbol\alpha_0|}$, and take $a=a'/1001^{\gamma|\boldsymbol\alpha_0|}$ in the transfer.

**Lemma 6.9 (harmonic odometer comparison)** <!-- C63 -->
- *Printed:* the comparison allows an infinite boundary supremum to be multiplied by a zero exit probability.
- *Problem:* the product $\infty\cdot 0$ is not controlled by the argument.
- *Correction:* add the premise $\sup_{\partial A\cap\overline{\Lambda^x_t}}v^{z}_t<\infty$. Every later application satisfies it.

**Lemma 6.13 (small odometer from low mass)** <!-- C64 -->
- *Printed:* the hypothesis is only that the annulus does not contain $z$.
- *Problem:* the component and odometer argument uses the whole closed ball, which must stay in $B_1$ and away from the pole.
- *Correction:* assume $\overline B_\rho(x_0)\subset B_1\setminus\{z\}$.

**Lemma 6.10 iteration, choice of $b$ (eq:choice-of-b; consequence at eq:choice-of-b-and-m0)** <!-- eq:choice-of-b -->
- *Printed:* $b:=2^{-2\beta^-/((C'\times C_3)\vee 1)}$, so that $b^{C'C_3N_0}=2^{-2\beta^-N_0\min(C'C_3,1)}$.
- *Problem:* when $C'C_3<1$ the first inequality of eq:choice-of-b-and-m0 is false. The radius count (at most $m\log_2/(2\log 7)+1<m/2$ radii, $m=N_0+j\ge 200$) makes $C'C_3<1/2$ unavoidable, and for $C'C_3\le 1/2$ the final bound fails for every $N_0$.
- *Correction:* $b:=2^{-2\beta^-/(C'\times C_3)}$. This gives $b^{C'C_3N_0}=2^{-2\beta^-N_0}$ and the Step 3 bound $b^{C'C_3(N_0+j)}\le 2^{-\beta^-}$. Replacing $\vee$ by $\wedge$ also works. The quantifier order is unaffected, since $C_3$ is given before $b$. If $C_3$ is treated as an input, the dependence statement should read "on $\gamma$, $\boldsymbol\alpha_0$ and $C_3$".

### Section 7: continuity of clusters

**Proposition 7.2 (continuity of clusters)** <!-- C18 -->
- *Printed:* $\Lambda_{t+\varepsilon}(z)\Subset\Lambda_t(z)+B_\delta(z)$, with $\delta=C\varepsilon^{1/(4\beta^-)}$.
- *Problem:* the ball $B_\delta(z)$ is centred at $z$. For $z\neq0$ and small $t$ the cluster lies in $B_{|z|/2}(z)$, so every $\lambda\in\Lambda_t(z)$ has $|\lambda|>\delta$ and $z\notin\Lambda_t(z)+B_\delta(z)$, although $z\in\Lambda_{t+\varepsilon}(z)$.
- *Correction:* $\Lambda_t(z)+B_\delta$, the ordinary $\delta$-neighbourhood, as in Proposition 5.2.

### Section 9: sub-harmonic balls

**Section 9.2, introduction to Lemma 9.3 (harmonic balls)** <!-- C22 -->
- *Printed:* every harmonic ball "in the sense of eq:harmonic-ball" has boundary in the closure of a regularised cluster.
- *Problem:* the printed class of test functions is too narrow. Both examples use Lebesgue measure in place of $\mu_h$. Under the printed class, $B_1\setminus[1/2,3/4]$ (a slit) and $\{x\in B_1:|x|\notin C\}$ with $C$ a fat Cantor set satisfy the defining identity; the slit violates Lemma 9.1(2) and the fat Cantor set violates Lemma 9.3.
- *Correction:* "in the sense of Theorem 1.1", with the class of the corrected Theorem 1.1 ([C7]).

**Proposition 9.2 (uniqueness of sub-harmonic balls)** <!-- C51 -->
- *Printed:* the inclusion $\widehat\Lambda\subset A$ for the sub-harmonic ball $A$ of mass $t$.
- *Problem:* we have not proved the printed inclusion. At the last time a bounded hole disappears, the cluster may be a sub-harmonic ball that omits a nonempty set inside its regularisation. We do not claim a counterexample.
- *Correction:* $\Lambda^{B_R;z}_t\subset A\subset\widehat\Lambda^{B_R;z}_t$, with $\mu_h(A\setminus\Lambda^{B_R;z}_t)=\mu_h(\widehat\Lambda^{B_R;z}_t\setminus A)=0$, and $A=\widehat\Lambda^{B_R;z}_t$ when $A$ is a regular open set. The paper does not use this proposition.

### Section 10: crossings and complementary components

**Lemma 10.5 (crossing components)** <!-- C48 -->
- *Printed:* every crossing component of $U^c\cap A$ contains a crossing component of the cluster.
- *Problem:* we have not proved the printed statement for clusters with holes, where a crossing component can be a whole annulus inside another hole. We do not claim that it is false.
- *Correction:* a deterministic statement. Finitely many crossings at small scales give local connectedness, no cut points, and simple-loop boundaries for the complementary components (Torhorst's theorem; see Jolivet, Loridant and Luo, arXiv:1411.6776, Theorem 3.1).

**Proposition 10.6 (complementary components of clusters)** <!-- C49 -->
- *Printed:* the components of $B_1\setminus\overline{\Lambda^z_t}$.
- *Problem:* the outer component of $B_1\setminus\overline{\Lambda^z_t}$ has a disconnected frontier.
- *Correction:* the components of $\mathbb C\setminus\overline{\Lambda^z_t}$, for clusters with $\Lambda^z_t\Subset B_1$. The proof uses Lemma 10.1 and the corrected Lemma 10.5.

**Proposition 10.7 (boundary of full clusters)** <!-- C50 -->
- *Printed proof:* a combination of Lemma 5.7, Lemma 10.1, a union bound and Theorem 5.5.
- *Problem:* Lemma 5.7 is an equality in law for a fixed centre, and the printed proof does not justify passing to all centres.
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
- *Printed:* the separated-annulus probability bound is applied at the origin and transferred to the rooted field.
- *Problem:* the rooted frequency needs the rooted ergodic argument, which the printed proof uses through Lemma 8.3 without stating the rooted-field identity explicitly.
- *Correction:* the positive rooted frequency at $\alpha=\gamma$ is established by dilation ergodicity, and transferred by the rooted-field identity, stated explicitly.

**Lemma 11.8 (bump construction)** <!-- C37 -->
- *Printed:* the bump height $\log(MC_2/C_1)/\gamma$ and the drift comparison with a universal constant.
- *Problem:* the weight comparison depends on $\boldsymbol\alpha_0$. (A negative bump height is harmless; the nonnegative bump below is a simplification.)
- *Correction:* use a nonnegative bump of height $\log\max\{1,2MC_2/C_1\}/\gamma$, and the comparison factor $1201^{-\gamma|\boldsymbol\alpha_0|}$.

**Pinch-event geometry (before Lemma 11.12)** <!-- C42 -->
- *Printed:* eq:metric-delta0-choice gives explicit buffers for $U$, $V$, $W$, $T$, $Q'$ and $Q$, but not $B_{10\delta_0}(W)\Subset T$ (it has $B_{10\delta_0}(W)\Subset\mathcal A_{1,2}$).
- *Problem:* the locality, bump-support and path-connection arguments of the replacement require the separation $B_{10\delta_0}(W)\Subset T$.
- *Correction:* add $B_{10\delta_0}(W)\Subset T$ to eq:metric-delta0-choice; the connected component $\Omega$ used in the replacement argument is specified in the text.

**Lemma 11.12 (pinch positive probability)** <!-- C43 -->
- *Printed:* the statement is for $\alpha_0=0$ and $P[\tilde G_1(0)]>0$.
- *Problem:* the tilde denotes a different event, and the rooted transfer needs $\alpha=\gamma$.
- *Correction:* for every $\alpha<Q$ and every $M>0$ there is an event $E^\alpha(M)\subset\widehat G_1^{h^\alpha}(0;M)$, measurable with respect to $h^\alpha|_{B_7}$ and invariant under additive constants, with $P[E^\alpha(M)]>0$; proved with local certificates.

**Proofs of Lemma 11.12 and Lemmas 11.15–11.17 (pinch-event proofs)** <!-- C44 -->
- *Printed:* four defects. (i) The bump in the proof of the third event sets $\tilde h=h+\frac{\phi}{\xi}\log\big(\frac{C_2}{C_1}\wedge1\big)$ (lines 3475–3478); if $C_2\ge C_1$ then $\tilde h=h$, and the chain $\operatorname{diam}\le\frac{C_2}{C_1}\operatorname{diam}\le D_h$ fails. (ii) The support condition $\phi\equiv0$ on $(U\cup B_{4\delta_0}(W))^c$ (line 3461) says nothing on $U\subset W$, yet $\phi\equiv0$ on $U$ is used at line 3481. (iii) The event of eq:large-mass-low-diam (lines 3410–3413) has the threshold $e^{-\xi\sup_W\varphi}$, where $\varphi$ is the harmonic extension of the GFF boundary data; $\sup_W\varphi=+\infty$ almost surely, so the threshold is $0$ and the event is empty. (iv) The thresholds of Lemma 11.16 depend on the conditioning and use non-strict inequalities (campaign GRAPH.md G43).
- *Problem:* each defect breaks a step of the printed argument; the proofs as printed do not establish Lemma 11.12 or Lemmas 11.15–11.17.
- *Correction:* replace these proofs by local certificates and a joint large-mass, small-diameter construction, with the bump factor, the support on $U$ and the thresholds repaired in the same step. The inner separation $(v-\delta)-(u+\delta)>8\delta$ is unchanged.

**Lemma 11.13 (many pinch scales)** <!-- C45 -->
- *Printed:* the proof uses positive probability at $\alpha=0$ directly for typical points, and transfers the frequency from the unrooted field; global metric events are treated as if they were annular-local.
- *Problem:* the rooted law has a logarithmic singularity, and global metric events are not annular-local.
- *Correction:* the proof uses dilation ergodicity, the certificate at $\alpha=\gamma$, and the rooted-field transfer. The statement is unchanged.

**Proposition 11.11 (clusters are not metric balls)** <!-- C46 -->
- *Printed:* the proof argues with a metric ball centred at $0$ and with a loose union over times.
- *Problem:* metric balls can have arbitrary centres, and the exceptional set of times is random.
- *Correction:* the proof treats arbitrary metric centres and proves the boundary-union identity through arrival times. The statement is as printed.

**Proposition 11.2 (non-Lipschitz clause of Theorem 1.2), eq:mass-times** <!-- C70 -->
- *Printed:* the passage from intervals to all Lebesgue measurable sets is a "standard machine" argument.
- *Problem:* the set function $A\mapsto\mu_h(\bigcup_{t\in A}\partial\widehat\Lambda_t)$ is not additive, and the interval computation gives only an inclusion up to a null set.
- *Correction:* for every Lebesgue measurable $A$, eq:mass-times is the boundary-union identity of Section 11, proved by arrival times.
- *Open:* measurability of the cone-condition set $A$ in the corrected Proposition 11.2 is not yet proved.

### Appendix A

**Standing volume-growth condition (Appendix A)** <!-- C65 -->
- *Printed:* both sides of the condition $r^{\beta^-}\le\mu(B_r(z))\le r^{\beta^+}$ use $\beta^-$.
- *Problem:* the upper bound must use $\beta^+$.
- *Correction:* $r^{\beta^-}\le\mu(B_r(z))\le r^{\beta^+}$ for all $z\in B_R$.

## Part 2. Minor corrections

### Standing convention

**Dependence on $\boldsymbol\alpha_0$ (Propositions 6.1, 7.2, Lemmas 6.3, 6.7, 6.11, 10.1)** <!-- C69 -->
- *Printed:* the constants of these results are stated or justified as depending only on $\gamma$.
- *Problem:* by Lemma 2.4 and Lemma 6.4 they depend on $\boldsymbol\alpha_0$ as well. This is dependence bookkeeping.
- *Correction:* one standing convention, with the dependence on $\boldsymbol\alpha_0$ written out at each site.

### Section 1

**Theorem 1.1(a)** <!-- C6 -->
- *Printed:* $\mu_h(\partial\Lambda_t(x))=0$.
- *Correction:* $\mu_h(\partial\Lambda_t(z))=0$ (the variable $x$ is not bound).

### Section 3

**Lemma 3.4 (conservation of mass)** <!-- C53 -->
- *Printed:* the equality case assumes zero boundary mass for an undefined measure $\mu$.
- *Correction:* use $\mu_h$, the LQG measure used throughout Lemma 3.4.

**Lemma 3.3 (monotonicity of clusters)** <!-- C52 -->
- *Printed:* the statement omits the pole $z$ from both clusters and does not require $t>0$.
- *Problem:* the obstacle problem is defined only for $t>0$, and monotonicity compares clusters with the same centre.
- *Correction:* on an event of probability one, for all $0<t_1\le t_2$, $r>0$ and $z\in B_r$, we have $\Lambda^{B_r;z}_{t_1}\subseteq\Lambda^{B_r;z}_{t_2}$.

**Lemma 3.5 (cluster compatibility)** <!-- C54 -->
- *Printed:* the mass parameter $t$ is free in the statement.
- *Problem:* the event on which compatibility holds must not depend on $t$, so $t$ has to be quantified inside it.
- *Correction:* for each $R>0$, on an event of probability one: for all $t>0$, $s_1\le R$ and $z\in B_{s_1}$, if $\overline{\Lambda^{B_{s_2};z}_t}\subset B_{s_1}$ for some $s_2\in[s_1,R]$, then $\Lambda^{B_s;z}_t=\Lambda^{B_{s_2};z}_t$ for all $s\in[s_1,R]$.

### Section 4

**Lemma 4.2 (Hölder continuity of the odometer)** <!-- C55 --> *(minor: dependence bookkeeping)*
- *Printed:* the deterministic Hölder exponent depends only on $\gamma$.
- *Problem:* the local power law near the origin depends on the log-singularity strength $\boldsymbol\alpha_0$, so the exponent must depend on it as well.
- *Correction:* the exponent may depend on $\gamma$ and $\boldsymbol\alpha_0$. The random constant stays uniform in $t,z,x,y$.

### Section 6

**Equation (6.2) (good-annulus event, §6.1) and the proof of Lemma 6.4** <!-- C23 -->
- *Printed:* the good-annulus event asks that "$\mathcal B^u$ exits $\mathcal A_{3r,5r}(z)$ before exiting $Y$", for Borel sets $Y\subset\mathcal A_{3r,5r}(z)$; the proof of Lemma 6.4 uses the same wording.
- *Problem:* when $Y\subset\mathcal A_{3r,5r}(z)$, the strict event is empty, so the condition does not express what is intended.
- *Correction:* "exits $\mathcal A_{3r,5r}(z)$ no later than exiting $Y$", that is, the exit time of the annulus is at most the exit time of $Y$.

**Lemma 6.7 (very good annuli are hit)** <!-- C62 --> *(minor: dependence bookkeeping)*
- *Printed:* the dependence of $a$, $C^{\pm}_i$ and $N_1$ on $\boldsymbol\alpha_0$ and on the lower volume exponent $\beta^-$ is suppressed.
- *Problem:* the comparison with the singular field uses these dependencies, so they cannot be suppressed.
- *Correction:* $a=a(b,p,\gamma,\boldsymbol\alpha_0,\beta^-)$, the constants $C^{\pm}_1,C^{\pm}_2$ depend on $a,\gamma,p,\boldsymbol\alpha_0,\beta^-$, and $C_3>0$ is universal. The dependence of $N_1$ is displayed in the statement.

### Section 11

**Definition 11.1 (Lipschitz domain)** <!-- C12 -->
- *Printed:* the local graph description uses $U\cap B_r(x_0)$, where $U$ is not defined in the definition.
- *Correction:* $A\cap B_r(x_0)$, the set being defined.

**Lemma 11.6 (comparison chain)** <!-- C38 -->
- *Printed:* the reference is to the fixed-aspect-ratio definition of the annular potential.
- *Correction:* refer to the variable-aspect-ratio definition, since the potential has variable aspect ratio.

### Appendix A

**Obstacle $\beta_t$ (Appendix A)** <!-- C66 -->
- *Printed:* $\beta_t:\overline{B_1}\to\mathbb R\cup\{+\infty\}$.
- *Problem:* $\beta_t(0)=-\infty$, so the codomain is wrong, and the majorization condition at the pole should be stated explicitly (it is vacuous there).
- *Correction:* $\beta_t:\overline{B_1}\to\mathbb R\cup\{-\infty\}$, with the majorization condition at the pole stated as vacuous.

**Lemma A.5 (conservation of mass for obstacle clusters)** <!-- C67 -->
- *Printed:* the equality conclusion uses the LQG-specific measure $\mu_h$.
- *Problem:* the appendix is written for an arbitrary Radon measure $\mu$.
- *Correction:* for the measure $\mu$ fixed in the appendix: $\mu(\Lambda_t)\le t$ for $t>0$, and if $\overline{\Lambda_t}\subset B_1$ and $\mu(\partial\Lambda_t)=0$, then $\mu(\Lambda_t)=t$.

**Lemma A.6 (compatibility for obstacle clusters)** <!-- C68 --> *(clarification)*
- *Printed:* $t$ is free, $s_1$ may be nonpositive, and $s_2$ is not scoped as an arbitrary quantified radius.
- *Problem:* not an error. In a deterministic lemma a free $t$ reads as universal, and $s_1\le0$ makes the hypothesis vacuous; the statement is clarified.
- *Correction:* for every $t>0$, every $0<s_1\le R$ and every $s_2\in[s_1,R]$: if $\overline{\Lambda_{B_{s_2}}(t)}\subset B_{s_1}$, then $\Lambda_{B_s}(t)=\Lambda_{B_{s_2}}(t)$ for all $s\in[s_1,R]$.


## Part 3. Proof gaps

Each item is a gap in a printed proof, not a change of statement. Where the corrected draft repairs one, it carries a correction marker. Selection rule: Part 3 lists every printed gap or slip that we have checked against the printed lines and that is not a statement change; gaps recorded in our internal graph but not checked against the printed text are not listed, and the full list is available on request.

- **Lemma 3.2 and eqs. (laplacian-of-v), (laplacian-of-v-general).** The proofs use $\nu\ge0$ without justification. A short repair uses the argument in the proof of Lemma 6.10.
- **Lemma A.1, Step 3.** The inequality $\beta_t(x)+\varepsilon/2\ge\beta_t(y)$ on $B_\delta(x_0)$ fails at $x_0=0$, where $\beta_t(0)=-\infty$; the ball $B_\delta(0)$ needs a separate estimate.
- **Proposition 4.1, last claim.** The equality case of Lemma 3.4 needs $\mu_h(\partial\Lambda)=0$, which is not available in general. For $\overline\Lambda\subset B_1$, a repair uses the identity in the proof of Lemma A.5.
- **Lemma 4.3, proof.** The proof replaces $\int_O G_O(\cdot,x)\,d\nu(x)$ by an integral over $\Lambda$. For $\nu$ charging $O\setminus\Lambda$, this step needs a separate argument.
- **Theorem 1.1(b).** Propositions 5.2 and 7.2 give right-continuity of $t\mapsto\Lambda_t$ only. Left-continuity is neither stated nor proved.
- **Lemma 9.1.** "a domain strictly contained" must read "in $B_R$". The test function $-G_{B_R}(\cdot,x)$ takes the value $-\infty$, while the sub-harmonic potential of eq:sub-harmonic-potential is required to be real-valued.
- **Proposition 9.2, proof.** The identity $\mu_h(\widehat\Lambda^{B_R;z}_t)=t$ uses Proposition 8.1 scaled to $B_R$ and Lemma 3.4. Neither is cited.
- **Proposition 7.2, covering near the origin.** The grid of Proposition 6.1 excludes $B_{10\sqrt\delta}(0)$, so the covering of the shell near the origin is not justified.
- **Proposition 7.2, mass equality.** "$\mu_h(\Lambda^z_t)=t$ by Lemma 3.4" also needs $\mu_h(\partial\Lambda^z_t)=0$, which is Proposition 8.1.
- **Lemma 11.6.** The time $t$ is free and "a.s." is missing. The verbatim extension of Lemmas 6.8 and 6.10 to $B_R$ also needs $\mathcal A_{0.5r,6r}(z)\subset B_R$.
- **Proposition 1.3.** "For each fixed $t\geq0$" (line 180) should read $t>0$.
- **Proposition 4.1, proof.** The lower bound (lines 704–708) compares with $t\log|x-z|$; the Green-function term is $-tG$.
- **Lemma 4.2, proof (lines 730–733).** A constant uniform in $t$ and $z$ needs a quantitative form of Proposition 2.5 (a Hölder bound $C(h)\|f\|_\infty$), which the printed proof does not supply.
- **Proposition 2.5 and Appendix A (lines 534, 3529–3530).** "Finiteness follows immediately from Lemma 2.4" and "follows from Lemma 2.4 and the scaling properties" need an almost-sure, all-scales, all-centres version of the volume-growth bound; it is not written.
- **Propositions 6.1, 6.2 and 8.1 (lines 1067, 1079, 2124).** The time $t$ is free in the statements; they must be read as holding for all $t$.
- **Measurability of $E_r(z)$ (lines 1117–1123).** $E_r(z)$ quantifies over all Borel sets $Y$, an uncountable family. The printed text asserts $E_r(z)\in\sigma(h|_{\mathcal A_{3r,5r}(z)})$ (line 1123) without proof, and Lemmas 6.3–6.7 need it.
- **Lemma 6.11 (line 1569) and Propositions 6.1–6.2 (lines 1593–1595).** Lemma 6.11 and Lemma 6.6 each produce an existential universal constant $C_3$; as printed the two need not match, and the combination needs $C_3$ of Lemma 6.6 to dominate that of Lemma 6.11.
- **Lemma 6.11, base case (lines 1898–1900).** Lemma 6.10 is applied on $\mathcal A_{\rho/4,2\rho}(x_0)$, which need not lie in $B_1\setminus\{z\}$ (the hypothesis is only $\overline{B_\rho(x_0)}\subset B_1\setminus\{z\}$); as printed the inequality is false when $\operatorname{dist}(z,B_\rho(x_0))\to0$.
- **Lemmas 6.11 and 6.13, components (lines 1772, 1834–1836, 1842).** The statements take $\widetilde\Lambda$ to be a component of $\Lambda\cap B_\rho(x_0)$, but the proofs switch to a component of $\Lambda\cap\mathcal A_{\rho/2,\rho}(x_0)$ with a different goal.
- **Lemma 6.11, constants (lines 1859, 1899, 1916).** The constant bookkeeping (the factor $1/(C_1^-\vee1)$ at line 1899 and the choice of $N_0$ at line 1916) fails for $C_1^-<1$.
- **Proposition 5.6, proof (lines 2432–2434).** "As the family $\{A_t\}$ continuously decreases to $\{z\}$" does not yield that $B$ is disjoint from $A_{s_0}$: the hypothesis gives the intersection $\{z\}$ only for open sets.
- **Proposition 7.1, covering near the origin (lines 1975–1981).** The grid of Proposition 6.1 excludes $B_{10\sqrt\varepsilon}(0)$, so the covering of $\partial B_{r/2}(z)$ by eq:cover-inner-ball is not justified for $z$ with $\big||z|-r/2\big|<9\sqrt\varepsilon$.
- **Proposition 8.1, parameters (lines 2231–2233).** One parameter tuple is used for Lemmas 6.7, 6.11, 8.2 and 8.3, but the order of choice of $C_3$, $b$, $a$, $C^\pm$, $N_0$, $\alpha$ and $m$ is not given.
- **Lemma 10.1 (lines 2496–2502).** The hypothesis $\overline{B_\rho(x_0)}\subset B_1\setminus\{z\}$ of Proposition 6.2 is never checked: $w$ may lie near $\partial B_1$, so $B_\rho(x_0)$ need not lie in $B_1$. The statement "for every $t>0$ and $z\in\mathbb C$" (line 2498) should read $z\in B_1$.
- **Lemma 11.10, eqn-shifted-field-weyl (lines 3041–3044).** The triangle inequality through $\overline G$ gives $3\varepsilon/2$, not $\varepsilon$, for the diameter bound on $\mathsf S_2$.
- **Section 2 (line 431) and Proposition 11.9 (lines 3036, 3071): $D_h$ for $\boldsymbol\alpha_0\neq0$.** Section 2 defines $D_{h+f}$ only for continuous $f$; for $\boldsymbol\alpha_0\neq0$ the field $h$ is not of that form near $0$, yet Weyl scaling of $D_h$ is used at lines 3036 and 3071.