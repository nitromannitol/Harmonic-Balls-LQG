# Section 11 approved replacement texts

Author-approved 2026-11-06; preserved verbatim from the audited standalone submissions. These are full proof sources, not a claim that every replacement is already integrated in the corrected paper.

## Lemma 11.8

```tex
\documentclass[12pt]{amsart}
\usepackage{amsmath,amssymb,amsfonts,fullpage,enumitem,hyperref}
\newtheorem{lemma}{Lemma}
\newtheorem{prop}[lemma]{Proposition}
\newtheorem{remark}[lemma]{Remark}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\Pp}{\mathbb P}
\newcommand{\E}{\mathbb E}
\newcommand{\A}{\mathbb A}
\newcommand{\dist}{\operatorname{dist}}
\newcommand{\SG}{\operatorname{SG}}
\newcommand{\osc}{\operatorname{osc}}
\title{A complete replacement for Lemma 11.8\\in Harmonic balls in Liouville quantum gravity}
\author{Proof audit and replacement}
\date{November 6, 2026}
\begin{document}
\maketitle

\section{Statement, conventions, and verdict}
Fix $\gamma\in(0,2)$ and $\alpha<Q:=2/\gamma+\gamma/2$.
Let $g$ be the whole-plane GFF with $g_1(0)=0$, and set
$h=g-\alpha\log|\cdot|$. Write $\A_{a,b}(z)=B_b(z)\setminus
\overline B_a(z)$. A cone below has a strictly positive angular opening
$\vartheta\in(0,2\pi)$. Including or excluding its two boundary rays makes
no difference to the assertions. For $r>0$ define, without suppressing
the underlying field,
\[
 S_h(r,z):=\sup_{x\in\A_{3r,6r}(z)}
 \int_{\A_{3r,6r}(z)}G_{B_{6r}(z)}(x,w)\,\mu_h(dw).
\]
Here $\Delta G_D(x,\cdot)=-\delta_x$; changing the common normalization
of $G$ only changes $M$. This is the variable-aspect-ratio quantity in
the source's equation \texttt{eq:alternate-size-2-full}, not its
one-parameter special case. Put
\[
 \widetilde G_r(z;M,\mathcal Q)
 =\{\mu_h(\A_{r,2r}(z)\cap(z+\mathcal Q))\ge M S_h(r,z)\}.
\]
Use $r=2^{-n}$ for the discrete scale index; the two meanings of a
subscript $1$ should not be interchanged in a proof.

\begin{prop}[Corrected and strengthened Lemma 11.8]\label{prop:B}
There is a positive nonincreasing function
$p_{\gamma,\vartheta}:(0,\infty)\to(0,1)$ such that, for every
$z\in\C$ and every $r>0$ satisfying
\[
 \dist(\A_{r,6r}(z),0)>r/100,
\]
one has
\begin{equation}\label{eq:B-bound}
 \Pp[\widetilde G_r(z;M,\mathcal Q)]
 \ge p_{\gamma,\vartheta}\bigl(1201^{\gamma|\alpha|}M\bigr)>0.
\end{equation}
The bound is independent of $z,r$, and the orientation of $\mathcal Q$.
For $\alpha=0$ the probability itself is independent of $z,r$ and
orientation, with no separation condition. For $z=0$ one may replace
$1201$ by $6$, for every $r>0$.

Consequently the printed assertion holds with
$p_M=p_{\gamma,\alpha,\vartheta,M}$; no threshold $N(z)$ is needed once
the displayed separation condition is imposed. For $z\ne0$, that
condition certainly holds for all $n\ge0$ with
$2^{-n}\le |z|/12$; for $z=0$ it holds for all $n$.
\end{prop}

Thus the assertion is true for each fixed cone and fixed parameters.
The notation $p_M$ must not mean a bound uniform over all cones, all
$M$, or all $\alpha<Q$. Each of these three stronger interpretations
is false; counterexamples are given below.

\section{Inputs and two elementary observations}
We use the defining locality, Weyl and coordinate-change properties
of the LQG measure:
\[
 \mu_{f+c}=e^{\gamma c}\mu_f,\qquad
 \mu_{f+u}=e^{\gamma u}\mu_f,\qquad
 \mu_{f(a\,\cdot+z)+Q\log|a|}(A)=\mu_f(aA+z).
\]
The measure is locally finite, has full support, and has no atoms.
On every compact set away from a prescribed logarithmic singularity,
almost surely there are $b>0$ and $K<\infty$ such that
$\mu_f(B_s(x))\le Ks^b$ for all sufficiently small $s$, uniformly in
$x$ in that compact set. These are the measure and volume properties
already assumed in the paper. The exact volume input needed here is
the upper bound of Bou-Rabee--Gwynne, Lemma 2.4, (2.11),
p.~10 of arXiv:2208.11795v1, in the case $\alpha_0=0$:
for each $b\in(0,(2-\gamma)^2/2)$, with polynomially high
probability as $s\to0$, simultaneously for $x\in B_1$,
$\mu_g(B_s(x))\le s^b$.
Borel--Cantelli at dyadic $s$, followed by monotonicity in $s$,
gives an almost-sure bound with a finite random constant.
Deterministic translation and dilation give it on any fixed compact
set. On a compact set away from $0$, the multiplier
$|\cdot|^{-\gamma\alpha}$ is bounded, giving the assertion for $h$.
No volume exponent uniform at a prescribed logarithmic singularity
is used.
Equivalently, for the finiteness needed
here one can use the precise statement of Bou-Rabee--Gwynne,
Proposition 2.5, p.~11 of arXiv:2208.11795v1: the Green potential of
any bounded density with respect to $\mu_h$ in a smooth bounded domain
is finite and H\"older continuous in the domain.
The uniform finiteness and continuity needed for the annular
supremum are proved directly below, so no additional
boundary assertion is attributed to that proposition.

For completeness, the volume property directly proves the relevant
finiteness. On a fixed disk the nonnegative Green kernel is bounded by
$C+C\log^+(1/|x-w|)$. Splitting $|x-w|\le1$ into dyadic annuli gives
\[
 \sup_x\int\log^+\frac1{|x-w|}\,\mu_f(dw)
 \le C K\sum_{j\ge0}(j+1)2^{-jb}<\infty.
\]
The part away from the diagonal is bounded by local finiteness.
The same decomposition shows that its small-diagonal contribution
vanishes uniformly; continuity of the remaining integral proves
continuity of the potential. Hence the supremum defining $S_f$ is
measurable, since it can be taken over rational points, and is finite.
It is strictly positive: choose two small disks compactly inside the
annulus on whose product $G$ has a positive lower bound, and use full
support. The sector mass is also strictly positive and finite.

We also record the Gaussian shift formula rather than appealing to
unspecified absolute continuity. With
\[
 \|u\|_\nabla^2=\frac1{2\pi}\int_{\C}|\nabla u|^2\,d^2w,
 \qquad u\in C_c^\infty(\C),
\]
the law of $g+u$ modulo constants has density
\begin{equation}\label{eq:CM}
 L_u(g)=\exp\{(g,u)_\nabla-\tfrac12\|u\|_\nabla^2\}
\end{equation}
with respect to that of $g$ modulo constants. In particular
$\E L_u^2=e^{\|u\|_\nabla^2}$.
This is precisely Miller--Sheffield, \emph{Imaginary geometry IV},
Proposition 2.9, p.~49 of arXiv:1302.4738v2.
One can verify \eqref{eq:CM} without any field regularity assertion:
expand the isonormal Gaussian process in an orthonormal basis of the
Dirichlet space, use the finite-dimensional normal density, and pass
to the limit. The exponentials converge in $L^2$, since the squared
norms of the partial sums converge. The reverse shift gives mutual
absolute continuity. In the circle-average normalization replace
$g+u$ by $g+u-u_1(0)$; all events here are unchanged by this
renormalizing constant.

\section{Positive probability and its quantitative dependence}
First suppose $\alpha=0$. Write
\[
 A=\mu_g(\A_{1,2}\cap\mathcal Q),\qquad B=S_g(1,0).
\]
Choose $c_1=c_1(\gamma,\vartheta)>0$ and $c_2=c_2(\gamma)>0$ so that
\[
 \Pp[A<c_1]\le\tfrac14,\qquad \Pp[B>c_2]\le\tfrac14.
\]
Such choices exist by positivity and finiteness. Rotational invariance
allows the same $c_1$ for every orientation. Let
$u:\C\to[0,1]$ be a fixed smooth radial function equal to $1$ on a
neighborhood of $\overline{\A}_{1,2}$, with support in $\A_{1/2,5/2}$.
Set
\[
 t(M)=\gamma^{-1}\log\max\{1,2Mc_2/c_1\},\qquad
 v(M)=t(M)^2\|u\|_\nabla^2.
\]
On the event $\{A\ge c_1,\ B\le c_2\}$, which has probability at least
$1/2$, locality and Weyl scaling give
\[
 \mu_{g+t(M)u}(\A_{1,2}\cap\mathcal Q)
 =e^{\gamma t(M)}A\ge 2Mc_2\ge 2M S_{g+t(M)u}(1,0).
\]
The first inequality still holds when $t(M)=0$, by the definition of
$t(M)$. The annular potential is unchanged because $u=0$ on $\A_{3,6}$.
Let $F=\widetilde G_1(0;M,\mathcal Q)$, with $1$ here denoting
Euclidean radius. Cauchy--Schwarz applied to \eqref{eq:CM} yields
\[
 \tfrac12\le \Pp[g+t(M)u\in F]
 =\E[L_{t(M)u}1_F]
 \le e^{v(M)/2}\Pp[F]^{1/2}.
\]
One can sharpen this consequence of the Gaussian shift.
Write $s=\sqrt{v(M)}$ and, when $s>0$, put
$Z=(g,t(M)u)_\nabla/s$, which is standard normal under
$\Pp$. Let $\mathsf Q$ be the shifted law, with density
$L=e^{sZ-s^2/2}$ relative to $\Pp$.
Under $\mathsf Q$, $Z$ has law $N(s,1)$, so the event
$A_s=\{Z\ge s\}$ has $\mathsf Q$-probability $1/2$.
Since $L-e^{s^2/2}$ is nonnegative on $A_s$ and nonpositive
on its complement, pointwise
\[
 (1_F-1_{A_s})(L-e^{s^2/2})\le0.
\]
Taking expectations and using $\mathsf Q(F)\ge1/2$
gives $\Pp(F)\ge\Pp(A_s)$.
For $s=0$ this conclusion is simply $\Pp(F)\ge1/2$.
Thus, writing
$\overline\Phi(s)=(2\pi)^{-1/2}\int_s^\infty e^{-x^2/2}\,dx$,
we may take the positive nonincreasing bound
\begin{equation}\label{eq:p-formula}
 p_{\gamma,\vartheta}(M)=\overline\Phi(\sqrt{v(M)})
                   \ge\tfrac14e^{-v(M)}.
\end{equation}
The displayed comparison with the simpler exponential bound
also follows by applying Cauchy--Schwarz above to $A_s$.
The Gaussian-tail bound is the strongest consequence of
$\mathsf Q(F)\ge1/2$ alone: equality is attained for $F=A_s$.
No optimality claim about the actual sector-mass event is needed.
This also corrects the printed request for a nonnegative bump of
height $\gamma^{-1}\log(Mc_2/c_1)$, which can be negative.

To transport the event, set $F_{r,z}(w)=rw+z$ and
$g^{r,z}=g\circ F_{r,z}+Q\log r$. Brownian scaling gives exactly
\[
 G_{B_{6r}(z)}(F_{r,z}(x),F_{r,z}(w))=G_{B_6}(x,w).
\]
The coordinate-change formula therefore transforms both the sector
mass and $S_g(r,z)$ into their radius-one versions for $g^{r,z}$.
Their ratio is unchanged by additive constants. The law of
$g(r\,\cdot+z)$ modulo constants is the whole-plane GFF law.
This proves the asserted exact translation and scale invariance,
and rotation invariance handles the orientation.

Now take arbitrary $\alpha<Q$. For any set $E$ under consideration put
$m=\inf_E|w|$, $L=\sup_E|w|$. If
$E=\A_{r,6r}(z)$ satisfies the separation assumption, then $m>r/100$
and its Euclidean diameter is at most $12r$. Consequently
\[
 L\le m+12r,\qquad L/m\le1201.
\]
The weight $a(w)=|w|^{-\gamma\alpha}$ consequently satisfies
$\sup_Ea/\inf_Ea\le1201^{\gamma|\alpha|}$. Since $G$ is nonnegative,
\[
 \frac{\mu_h(\A_{r,2r}(z)\cap(z+\mathcal Q))}{S_h(r,z)}
 \ge
 1201^{-\gamma|\alpha|}
 \frac{\mu_g(\A_{r,2r}(z)\cap(z+\mathcal Q))}{S_g(r,z)}.
\]
Apply the already proved assertion with threshold
$1201^{\gamma|\alpha|}M$. For $z=0$, $L/m=6$ instead.
This proves Proposition~\ref{prop:B} in full.

\section{Uniformities that hold, and ones that do not}
Fix $\vartheta_0>0$, $A_0<\infty$, and $M_0<\infty$. For every cone
with opening at least $\vartheta_0$, every $|\alpha|\le A_0$ with
$\alpha<Q$, every $0<M\le M_0$, and every admissible $(z,r)$, a common
positive lower bound is
\[
 p_{\gamma,\vartheta_0}(1201^{\gamma A_0}M_0).
\]
Indeed every such cone contains a rotated cone of opening
$\vartheta_0$, and the event increases with the cone and decreases
with $M$. This gives all the stated uniformities without choosing
random thresholds in $z$ or $n$. It is a bound on each probability,
not an assertion that one event occurs simultaneously at all centers.

There is no positive bound uniform over arbitrary cone openings.
Take nested sectors $\mathcal Q_j$ whose openings decrease to zero
around a fixed ray. The LQG mass of that deterministic ray is zero:
on compact sets away from the origin the first moment measure is
absolutely continuous with respect to Lebesgue measure. In the present
normalization its density is $\max\{1,|w|\}^{\gamma^2}$, as follows by
taking the Gaussian expectation in the circle-average definition.
Continuity from above gives
$\mu_g(\A_{1,2}\cap\mathcal Q_j)\downarrow0$ almost surely.
Since $S_g(1,0)>0$ almost surely, the event probabilities tend to zero.
For a fixed cone, the ratio is finite almost surely, so its upper
tail tends to zero as $M\to\infty$.

There is also no uniform bound over $\alpha\in(-\infty,Q)$.
Set $\alpha=-a$, $a\to\infty$, and $z=0,r=1$. Directly from the
nonnegative Green kernel,
\[
 \frac{\mu_{g+a\log|\cdot|}(\A_{1,2}\cap\mathcal Q)}
 {S_{g+a\log|\cdot|}(1,0)}
 \le (2/3)^{\gamma a}
 \frac{\mu_g(\A_{1,2}\cap\mathcal Q)}{S_g(1,0)}
 \longrightarrow0\quad\hbox{almost surely}.
\]
These are counterexamples to uniform interpretations, not to the
fixed-parameter lemma.

\section{Consequences for the adjacent argument}
In the source's Lemma \texttt{lemma:mu\_h-bad-and-harnack}, the density
constant must be written $\delta(\gamma,\alpha,\vartheta,M)$ when
asserted for a field rooted at a prescribed point. At a
$\mu_h$-typical point the local singularity is $\gamma$, so one may
use $\delta(\gamma,\vartheta,M)$. The dependence on the cone cannot be
removed. Only a countable family of cones is needed for the
subsequent cone-condition argument. The appropriate inclusion is:
every open cone contains a smaller cone with rational extremal
directions. The source's use of a containing rational cone reverses
the monotonicity needed for a lower bound on sector mass.
No uniformity over that countable family is required.

\begin{thebibliography}{9}
\bibitem{HB}
A.~Bou-Rabee and E.~Gwynne,
\emph{Harmonic balls in Liouville quantum gravity},
\href{https://arxiv.org/pdf/2208.11795v1}{arXiv:2208.11795v1}.
Inputs: the upper volume bound in Lemma 2.4, (2.11), p.~10,
used only at $\alpha_0=0$; and the Green-potential statement
in Proposition 2.5, p.~11.
\bibitem{IG4}
J.~Miller and S.~Sheffield,
\emph{Imaginary geometry IV: interior rays, whole-plane reversibility,
and space-filling trees},
\href{https://arxiv.org/pdf/1302.4738v2}{arXiv:1302.4738v2}.
The Gaussian shift formula used here is Proposition 2.9, p.~49.
\end{thebibliography}
\end{document}
```

## Lemma 11.13 and consequences

```tex
\documentclass[12pt]{amsart}
\usepackage{amsmath,amssymb,amsfonts,fullpage,enumitem,hyperref}
\newtheorem{lemma}{Lemma}
\newtheorem{prop}[lemma]{Proposition}
\newtheorem{theorem}[lemma]{Theorem}
\newtheorem{remark}[lemma]{Remark}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\E}{\mathbb E}
\newcommand{\Pp}{\mathbb P}
\newcommand{\A}{\mathbb A}
\newcommand{\diam}{\operatorname{diam}}
\newcommand{\dist}{\operatorname{dist}}
\newcommand{\len}{\operatorname{len}}
\newcommand{\cl}{\operatorname{cl}}
\newcommand{\Leb}{\operatorname{Leb}}
\title{Positive probability of the pinch event and its consequences\\A replacement for Lemma 11.13}
\author{Proof audit and replacement}
\date{November 6, 2026}
\begin{document}
\maketitle

\section{Statement and precise geometry}
The labels, rather than the numbering of other versions, identify
the targets in the supplied source:
\texttt{lemma:mu\_h-pinch-positive-probability},
\texttt{lemma:mu\_h-pinch-bad}, and
\texttt{prop:not-metric-balls}. The first must say
$\Pp[\widehat G_1(0;M)]>0$, not $\widetilde G_1(0)$.
We distinguish a Euclidean radius $r$ from the integer index $n$:
the latter means $r=2^{-n}$.

Fix $\gamma\in(0,2)$, $Q=2/\gamma+\gamma/2$, and
$\xi=\gamma/d_\gamma>0$. For the moment set
$h^\alpha=g-\alpha\log|\cdot|$, where $g$ is a whole-plane GFF
with $g_1(0)=0$ and $\alpha<Q$. We will prove more than the
requested $\alpha=0$ case; the case $\alpha=\gamma$ is essential
for the subsequent quantum-typical-point assertion.

Choose the deterministic sets in the figure with the following
explicit buffer conditions. They are harmless specifications of
the intended keyhole geometry. The sets $U\Subset V\Subset W$
are concentric open disks in $\A_{1,2}$, with
$\overline W\subset T$, where $T$ is bounded, connected and open,
$\overline T\subset\A_{1,6}$, $T\subset\A_{1,5}$, and
$\partial B_5\subset\overline T$. The sets
$Q'\Subset Q$ are bounded connected open sets, with
$\overline Q\subset\A_{4,5}\setminus\overline T$.
Take a deterministic $\delta>0$ so small that
\begin{equation}\label{eq:buffers}
\begin{gathered}
 B_{10\delta}(\overline T)\Subset\A_{1,6},\qquad
 B_{10\delta}(\overline U)\Subset V,\qquad
 B_{10\delta}(\overline V)\Subset W,\\
 B_{10\delta}(\overline W)\Subset T\cap\A_{1,2},\qquad
 B_{10\delta}(\overline Q')\Subset Q,\qquad
 B_{10\delta}(\overline Q)\Subset
       \A_{4,5}\setminus B_{10\delta}(\overline T).
\end{gathered}
\end{equation}
We also take $\delta<10^{-3}$.
Take the component containing $0$ of the open set
\[
 B_7\setminus
 \bigl(\overline{B_{2\delta}(Q)}
             \cup\overline{B_{2\delta}(W)}\bigr)
\]
and call it $\Omega$. It contains $\{0\}\cup\partial B_5$ compactly.
Indeed $B_3\setminus\overline{B_{2\delta}(W)}$ connects $0$
to $T$ without approaching $Q$. The set
$T\setminus\overline{B_{2\delta}(W)}$ is connected by detouring
paths in the collar of $W$; a small neighborhood of this set,
still disjoint from $\overline{B_{2\delta}(Q)}$, reaches every
point of $\partial B_5$. Thus all these points belong to the
same component. These properties hold, for example, by taking a thin corridor
from a disk about $1.5$ to the annulus $\A_{4.8,5}$, taking their
union for $T$, choosing $U,V,W$ sufficiently small about $1.5$,
and choosing $Q',Q$ sufficiently small about $-4.4$.
Thus no inference depends on a drawing. The proof also applies
to any fixed sets having the buffer and connectivity properties
just listed.

For a field $f$ write
\[
 S_f(r,z)=\sup_{x\in\A_{3r,6r}(z)}
       \int_{\A_{3r,6r}(z)}G_{B_{6r}(z)}(x,w)\,\mu_f(dw).
\]
For $A_r(z)=z+rA$, define the event in the question by
\begin{equation}\label{eq:hatG}
\widehat G_r^f(z;M)=
\left\{
\begin{aligned}
 D_f(Q'_r(z),\partial Q_r(z))
      &>\sup_{x\in\partial B_{5r}(z)}D_f(z,x),\\
 D_f(z,\partial B_{5r}(z))
      &>\sup_{x,y\in T_r(z)}D_f(x,y),\\
 \mu_f(U_r(z))&>M S_f(r,z).
\end{aligned}\right.
\end{equation}
Distances between sets are infima, including when one set is open.
Continuity gives the same infimum after taking its closure.

\begin{theorem}\label{thm:positive}
For every fixed geometry above, every $\alpha<Q$, and every
$M>0$, there exists an event
$E^{\alpha}(M)\in\sigma(h^\alpha|_{B_7})$, invariant under adding
a constant to the field, such that
\[
 \Pp[E^{\alpha}(M)]>0,\qquad
 E^{\alpha}(M)\subset\widehat G_1^{h^\alpha}(0;M).
\]
The deterministic definition of the event does not depend on
$\alpha$. In particular the requested positive-probability
assertion is true with $\widehat G$ in place of $\widetilde G$.
\end{theorem}

\section{Inputs and elementary metric facts}
We use the following defining LQG properties, in exactly the
normalizations of the paper. The metric is a length metric
inducing the Euclidean topology; its internal metric on an open
set is determined by the field there. For a continuous $u$,
$D_{f+u}=e^{\xi u}\cdot D_f$, where the right hand side means
weighting path length by $e^{\xi u}$, and
$\mu_{f+u}=e^{\gamma u}\mu_f$. Both objects obey the coordinate
change $f(r\,\cdot+z)+Q\log r$. The measure has full support and
is locally finite. The annular potential $S_f$ is finite and
strictly positive. For the last assertion, the local volume
bound $\mu_f(B_s(x))\le Ks^b$ away from the logarithmic
singularity follows from the upper half of Lemma 2.4,
(2.11), p.~10 of Bou-Rabee--Gwynne,
arXiv:2208.11795v1, used only for $\alpha_0=0$:
the uniform bound on $B_1$ holds with polynomially high
probability for each $b\in(0,(2-\gamma)^2/2)$.
Apply Borel--Cantelli at dyadic radii, monotonicity, and
translation/dilation to obtain the almost-sure bound on
fixed compact sets. Weyl scaling then handles the bounded
logarithmic drift on the annulus. This bound and the estimate
$G\le C+C\log^+(1/|x-w|)$ give the summable bound
$CK\sum_{j\ge0}(j+1)2^{-jb}$, uniformly in $x$.
Positivity follows from full support and positivity of $G$.

Two additional metric inputs are from \cite{DFGPS},
arXiv:1905.00380v2:
\begin{enumerate}[label=(\roman*)]
\item Proposition 3.17, p.~43, says in particular that for
$\alpha<Q$ the metric for $g-\alpha\log|\cdot|$ is finite
and induces the Euclidean topology also at $0$.
\item Lemma 3.19, p.~45, equation (3.63), gives, for each compact
$K$, $0<s<\xi Q$, and a square $S_\ell(w)$ of side $\ell$,
\[
 \Pp\!\left[\sup_{u,v\in S_\ell(w)}
  D_g(u,v;S_\ell(w))>\ell^s c_1 e^{\xi g_1(0)}\right]
 \le \ell^{(\xi Q-s)^2/(2\xi^2)+o(1)}
\]
uniformly for $w\in K$. Constants from fixed changes of side
length have no effect below. Choosing $s<\xi(Q-2)$ permits a
union bound over $O(\ell^{-2})$ squares.
\end{enumerate}
These statements are used only for a small-box construction and
for the topology at a logarithmic singularity.

Here are elementary facts that resolve the locality issues.
In a length metric inducing the Euclidean topology, the internal
metric of a connected open set $O$ is finite and continuous on
$O\times O$. Indeed a sufficiently small metric ball about each
point lies in $O$, and nearly shortest paths between points of
a smaller ball cannot leave the larger one. Thus the internal
and ambient metrics agree locally. Chain such neighborhoods
along a path in $O$. Consequently a compact subset of $O$ has
finite internal diameter.

If $A\Subset O$, the distance $D_f(A,\partial O)$ depends only
on the metric in $O$. Every path from $A$ to $\partial O$ can
be cut at its first boundary hit. Conversely approximate
boundary endpoints from inside and use continuity. Likewise
\[
 D_f(\partial B_a,\partial B_b),\quad 0<a<b,
\]
depends only on the field in the open annulus $\A_{a,b}$, with
boundary values obtained by continuity. Cut a path at its last
visit to $\partial B_a$ before its first visit to $\partial B_b$.
In particular these crossing distances are unchanged by a field
perturbation supported away from the annulus. They are strictly
positive because the two boundary circles are disjoint compact
sets in a continuous metric.
These facts concern exit or crossing distances; arbitrary
point-to-point distances need not be local.

The events used below are jointly measurable in the field,
the center, and the scale. We spell out the internal-metric
point needed for this assertion and for the later Fubini step.
Fix an open set $O$, countable dense sets in $O$ and $O^c$,
and write $O_{z,r}=z+rO$.
For $v\in O_{z,r}$ put
\[
 \delta_{z,r}(v)=D_f(v,O_{z,r}^c)
       =\inf_{q\in\mathcal D_{O^c}}D_f(v,z+rq).
\]
This is positive and Borel in $(f,z,r,v)$.
On the countable vertex set $z+r\mathcal D_O$, augmented
by the two endpoints, allow a step $v\to w$ when
\[
 D_f(v,w)<\tfrac14
                \min\{\delta_{z,r}(v),\delta_{z,r}(w)\},
\]
and give that step cost $D_f(v,w)$.
The infimum of the costs of finite allowed chains equals
the internal distance in $O_{z,r}$.
For one inequality, nearly shortest ambient paths for an
allowed step cannot leave $O_{z,r}$, so its cost is the
internal distance between its endpoints.
For the other, a finite-length path in $O_{z,r}$ has compact
image with positive $D_f$-distance from the complement.
Partition it into sufficiently short subpaths and approximate
the partition points by the dense vertex set.
The resulting chain is allowed, and its cost differs from
the path length by an arbitrarily small amount.
Thus internal distance is a countable infimum of Borel
chain costs, with cost $+\infty$ for a nonallowed chain.
Its suprema on the compact sets below are measurable by
continuity and countable dense subsets of those sets.
Ordinary set distances are countable infima by continuity.
Finally, the mass terms are integrals of Borel functions
against the random measure. The potential is lower
semicontinuous in its first variable by Fatou's lemma,
so its supremum can be taken over a fixed countable dense
set of the rescaled annulus. These observations prove the
claimed joint measurability, including for the translated
local certificates.

We also make the Gaussian absolute-continuity input explicit.
For a smooth compactly supported $u$ the whole-plane GFF shift
has density
\begin{equation}\label{eq:CM-C}
 \exp\{(g,u)_\nabla-\tfrac12\|u\|_\nabla^2\},
 \qquad \|u\|_\nabla^2=(2\pi)^{-1}\int|\nabla u|^2,
\end{equation}
modulo constants. This is Miller--Sheffield,
arXiv:1302.4738v2, Proposition 2.9, p.~49.
Its positivity and the reverse shift give equivalence of laws.
The formula follows by expanding in an orthonormal basis of the
Dirichlet space and passing from finite-dimensional Gaussian
densities in $L^2$. It holds also for Dirichlet GFFs with
$u\in H_0^1$, and after a fixed deterministic logarithmic drift.

The domain Markov property used below is Proposition 2.8 of the
same reference, pp.~48--49: in a bounded open $W$, conditional
on the outside field, the inside field is an independent
zero-boundary GFF plus the harmonic extension of the outside
data. All our resampling disks avoid the normalization circle
and the logarithmic singularity.
In particular, if $K\Subset W$, the conditional law on a
neighborhood of $K$ is equivalent to its unconditional law.
To verify the last statement, write the field as $g_W+H$.
For each realized harmonic $H$, cut it off smoothly inside $W$
while keeping it unchanged near $K$. This is a finite-Dirichlet-
energy shift, so the restriction of $g_W+H$ is equivalent to
that of $g_W$. The same is true for every value of $H$ and hence
for its mixture, the marginal law. This argument uses only
bounds on compact subsets of $W$, not an unjustified bound
on $\sup_W H$.

\section{A complete small-diameter, large-mass construction}
\begin{lemma}\label{lem:massdiam}
Let $U_0\Subset V_0\Subset O$ be concentric disks, with
$\overline O\Subset W_0$, where $W_0$ is a disk avoiding $0$
and the normalization circle. For every $c,\epsilon>0$,
\[
 \Pp\!\left[
   \mu_{h^\alpha}(U_0)>c,\quad
   \diam_{h^\alpha}(\overline V_0;O)<\epsilon
 \right]>0.
\]
The conditional probability of the same event, given the field
outside $W_0$, is strictly positive almost surely.
\end{lemma}
\begin{proof}
We first prove the unconditional assertion, using deterministic
shifts supported in $W_0$. Choose a closed dyadic square
$S_0\Subset U_0$. Its mass is positive almost surely.
A nonnegative bump equal to a large constant on $S_0$ makes
its mass exceed $8c$ on an event of positive probability.
Formula \eqref{eq:CM-C} transfers this event back to the original
field. Denote its probability by $p>0$.

Tile $S_0$ by dyadic squares $S$ of side $\ell=2^{-n}$, and
divide the tiles into four classes according to the parities
of their two grid coordinates. For each tile let $H_S$ and
$J_S$ be concentric squares of sides $3\ell/2$ and $7\ell/4$.
The closures of the $J_S$ for one class are pairwise disjoint.
For large $n$ all are contained in $U_0$.
The square-diameter estimate above, with
$s<\xi(Q-2)$, and a union bound show that with probability
tending to one all the $\overline H_S$ have internal diameter
less than $\epsilon/8$ in $J_S$.
For $h^\alpha$ the same assertion follows by Weyl comparison
on the fixed compact region, where $-\alpha\log|\cdot|$ is
bounded and smooth. Endpoints on $\partial H_S$ cause no issue
because $\overline H_S\subset J_S$.

Fix a deterministic $n$ for which this event and
$\{\mu_{h^\alpha}(S_0)>8c\}$ have intersection of probability
at least $p/2$. Some one of the four classes has mass greater
than $2c$ there, so a deterministic class $i$ has this property
jointly with the diameter event with probability at least $p/8$.
Let $\mathcal S$ be this finite class and put
\[
 K=\overline V_0\setminus\bigcup_{S\in\mathcal S}\operatorname{int}H_S.
\]
The squares removed are disjoint and compactly inside $V_0$.
Hence $K$ is connected, and $O\setminus\bigcup S$ is connected.
There exists a connected open $O_0$ with
$K\subset O_0\Subset O\setminus\bigcup S$.
For example cover $K$ by finitely many sufficiently small
Euclidean disks in that open set and join the finitely many
components by finitely many paths there.
The internal diameter of $K$ in $O_0$ is finite almost surely,
by the elementary metric fact above. Thus for some deterministic
$A<\infty$ the same positive-probability event also has that
diameter at most $A$.

Choose a smooth $\varphi:\C\to[0,1]$, supported in $W_0$, equal
to $1$ on $\overline O_0$ and $0$ on every $S\in\mathcal S$.
Subtract
\[
 \xi^{-1}\log\max\{1,4A/\epsilon\}\,\varphi
\]
from the field. The mass of $\bigcup S$ is unchanged and
remains greater than $2c$. All metrics decrease. The diameter
of $K$ using paths in $O_0$ becomes at most $\epsilon/4$.
A point of $\overline V_0$ outside $K$ belongs to some $H_S$
and can be joined to $\partial H_S\subset K$ inside $J_S$ at
cost less than $\epsilon/8$. Applying this to both endpoints
and then joining through $K$ gives total cost less than
$\epsilon/2<\epsilon$, using paths in $O$.
Absolute continuity transfers the resulting positive-probability
event back to $h^\alpha$.

This proof avoids the factor-of-three loss in the printed
small-square argument, which gives only $3\epsilon/2$ if its
three contributions are each bounded by $\epsilon/2$.
Finally the event just proved is determined by the restriction
to $O\Subset W_0$. The conditional-equivalence argument following
\eqref{eq:CM-C} proves its strictly positive conditional
probability. This completes both assertions.
\end{proof}

\section{Three local certificates}
For the rest of the construction write $D=D_{h^\alpha}$ and
$\mu=\mu_{h^\alpha}$. Define the compact connected sets
\[
 K_0=\overline{T\setminus B_{3\delta}(W)},\quad
 K_1=\overline V,\quad
 K_2=\overline{B_{3\delta}(W)\setminus V},
 \qquad O_i=B_\delta(K_i),
\]
and put $d_i=\diam_D(K_i;O_i)$.
Removing a disk compactly contained in a connected planar open
set leaves it connected: a path through the disk can be
rerouted in a thin surrounding annulus. This proves the asserted
connectedness for $K_0$; the others are immediate. Thus all
$d_i$ are finite. The buffers imply
$\overline O_1\subset W$, $O_0\cap W=\varnothing$, and
$\overline O_2\subset B_{4\delta}(W)\setminus
\overline{B_\delta(U)}$.
Write
\[
 a_0=D(0,\partial B_\delta),\quad
 a_1=D(\partial B_\delta,\partial B_{2\delta}),\quad
 a_2=D(\partial B_{2\delta},\partial B_{3\delta}),
\]
\[
 L=D(\overline Q',\partial Q),\qquad
 A=\sup_{x\in\partial B_5}D(0,x;\Omega),\qquad
 S=S_{h^\alpha}(1,0).
\]
All these quantities are positive and finite. Define
\begin{equation}\label{eq:Es}
 E_1=\{L>A,\ a_0>d_0\},\qquad
 E_2=\{a_1>d_1,\ \mu(U)>MS\},\qquad
 E_3=\{a_2>d_2\}.
\end{equation}
Each event is measurable with respect to the field in $B_7$.
For $L$ and the $a_i$ this follows from the first-exit and
crossing observations; all upper bounds use explicitly internal
metrics in the indicated subsets of $B_7$. All three events
are invariant under adding a constant: metric comparisons
scale by $e^{\xi c}$ and the mass comparison by $e^{\gamma c}$.

\begin{lemma}\label{lem:include}
The event $E_1\cap E_2\cap E_3$ implies
$\widehat G_1^{h^\alpha}(0;M)$.
\end{lemma}
\begin{proof}
The first inequality follows from
$L>A\ge\sup_{\partial B_5}D(0,x)$.
Every path from $0$ to $\partial B_5$ must cross successively
the three concentric regions defining the $a_i$.
By cutting it into successive subpaths, then taking infima,
\[
 D(0,\partial B_5)\ge a_0+a_1+a_2>d_0+d_1+d_2.
\]
This is a path-crossing lower bound, not a reverse triangle
inequality. Further,
$\overline T=K_0\cup K_2\cup K_1$, with
$K_0\cap K_2\ne\varnothing$ and $K_2\cap K_1\ne\varnothing$.
Joining through these intersection points gives
$\diam_D(T)\le d_0+d_2+d_1$. The strict second inequality
of \eqref{eq:hatG} follows. The third is part of $E_2$.
\end{proof}

\begin{lemma}\label{lem:E1}
$\Pp[E_1]>0$.
\end{lemma}
\begin{proof}
Choose deterministic $c_1,c_2,c_3,c_4>0$ so that
\[
 F=\{L\ge c_1,\ A\le c_2,\
      D(0,\partial B_{\delta/2})\ge c_3,\ d_0\le c_4\}
\]
has positive probability. This is possible since the variables
are positive and finite. Let $\varphi_Q,\varphi_0$ be smooth
functions taking values in $[0,1]$, with
\[
 \varphi_Q=1\ \hbox{on }\overline Q,\quad
 \operatorname{supp}\varphi_Q\subset B_\delta(Q),\qquad
 \varphi_0=1\ \hbox{on }\overline B_{\delta/2},\quad
 \operatorname{supp}\varphi_0\subset B_\delta.
\]
Set $b=\max\{1,2c_4/c_3\}$ and
$b_Q=b\max\{1,2c_2/c_1\}$, and add
$\xi^{-1}\log b_Q\,\varphi_Q+
 \xi^{-1}\log b\,\varphi_0$ to the field.
The $Q$ bump is disjoint from $\Omega$. The root bump multiplies
all lengths in $\Omega$ by at most $b$. Thus $A_{\rm new}\le bA$.
The first-exit observation gives $L_{\rm new}=b_Q L$,
since the $Q$ bump is constant on all of $Q$.
On $F$ we consequently have
$L_{\rm new}\ge2bc_2>A_{\rm new}$.

Every path from $0$ to $\partial B_\delta$ first crosses
$\partial B_{\delta/2}$ while the root bump has its constant
value. Hence
$a_{0,\rm new}\ge bD(0,\partial B_{\delta/2})\ge2c_4>d_0$.
The internal metric defining $d_0$ is unchanged, as both bumps
vanish on $O_0$. This proves $E_1$ for the shifted field on $F$.
Formula \eqref{eq:CM-C} gives $\Pp[E_1]>0$ for the original field.
\end{proof}

\begin{lemma}\label{lem:E2}
For every $M>0$, $\Pp[E_1\cap E_2]>0$.
\end{lemma}
\begin{proof}
The event $E_1$, the crossing distance $a_1$, and $S$ are
measurable with respect to the field outside $W$. For $E_1$
this uses the explicit exclusion of $B_{2\delta}(W)$ from
$\Omega$ and the fact that $O_0$ avoids $W$.
Choose deterministic $c_1,c_2>0$ for which the outside event
\[
 F=E_1\cap\{a_1\ge c_1,\ MS\le c_2\}
\]
has positive probability. By Lemma~\ref{lem:massdiam}, the event
\[
 H=\{d_1<c_1/2,\ \mu(U)>2c_2\}
\]
has positive conditional probability almost surely given the
field outside $W$. The geometry in that lemma is precisely
$U,V,O_1,W$. Therefore
\[
 \Pp[F\cap H]=
 \E[1_F\,\Pp(H\mid h^\alpha|_{W^c})]>0.
\]
On $F\cap H$ both inequalities of $E_2$ are strict. This proves
the assertion without an unbounded harmonic correction
$\sup_W H$, and without replacing strict inequalities by
nonstrict ones.
\end{proof}

\begin{lemma}\label{lem:E3}
For every $M>0$, $\Pp[E_1\cap E_2\cap E_3]>0$.
\end{lemma}
\begin{proof}
Choose deterministic $c_1,c_2>0$ such that
\[
 F=E_1\cap E_2\cap\{a_2\ge c_1,\ d_2\le c_2\}
\]
has positive probability. Take a smooth $\varphi:\C\to[0,1]$
equal to $1$ on $\overline O_2$, equal to $0$ on $\overline U$,
and supported in $B_{5\delta}(W)$. The buffers guarantee that
these prescriptions are compatible. Put
\[
 k=\min\{1,c_1/(2c_2)\},\qquad
 h_{\rm new}=h^\alpha+\xi^{-1}\log k\,\varphi .
\]
The perturbation is nonpositive, so every internal distance
decreases. On $O_2$ it is constant, so $d_{2,\rm new}=kd_2$.
The crossing distances $a_0,a_1,a_2$ and $L$ are unchanged,
by their locality and the disjoint support. Consequently on $F$,
$d_{2,\rm new}\le c_1/2<a_{2,\rm new}$.
The upper quantities $A,d_0,d_1$ decrease, so $E_1$ and the
first inequality of $E_2$ persist. The masses of $U$ and
$\A_{3,6}$ are unchanged, so the other inequality persists too.
The shifted field satisfies all three events on $F$.
Absolute continuity proves the lemma.
\end{proof}
Lemmas~\ref{lem:include}--\ref{lem:E3} prove
Theorem~\ref{thm:positive}. Notice the reciprocal and the factor
$2$ in $k$: the printed $\min\{1,c_2/c_1\}$ cannot yield the
claimed shrinking estimate.

\section{Scale ergodicity, including the logarithmic singularity}
We supply the ergodicity argument; stationarity by itself would
not imply a positive almost-sure frequency.

\begin{lemma}\label{lem:mixing}
On whole-plane fields modulo constants, the dilation
$\mathcal T g=g(\cdot/2)$ is mixing, hence ergodic.
The same holds on the law of $h^\alpha$ for every fixed
$\alpha$, since its deterministic logarithmic drift changes
by a constant under dilation.
\end{lemma}
\begin{proof}
For smooth compactly supported real test functions $f,k$ of
integral zero, with the support of $f$ bounded away from $0$,
the covariance kernel of the whole-plane GFF gives
\[
 \operatorname{Cov}\big((g,f),(\mathcal T^n g,k)\big)
 =-\iint f(x)k(y)\log|x-2^{-n}y|\,d^2x\,d^2y
 \longrightarrow0.
\]
Indeed the integrand's logarithm equals
$\log|x|+O(2^{-n})$ uniformly on the two supports for large $n$,
and the first term integrates to zero against $k$.
Terms depending on only one variable in the normalized covariance
kernel vanish because both tests have integral zero.
The same calculation applies to any two finite vectors of
such field evaluations. Their joint Gaussian covariance matrices
converge to block diagonal matrices, so their joint laws
converge to the product law.

Tests supported away from $0$ generate the field modulo constants:
cut out a disk of radius tending to zero from any test, and
correct its integral by a smooth test away from $0$. The
variance of the discarded pairing tends to zero by local
integrability of the logarithmic covariance kernel. A countable
dense collection of these tests generates the Gaussian
$\sigma$-algebra. Approximate arbitrary bounded measurable
functions in $L^2$ by bounded continuous functions of finitely
many tests; finite-dimensional Gaussian measures are regular,
so these cylinder functions are dense. Dilation
preserves the $L^2$ norm, so Cauchy--Schwarz transfers the
factorization of correlations to arbitrary bounded measurable
functions. This is mixing. If an event is invariant, its
probability equals the limiting correlation with itself and
hence is its own square; this is ergodicity.
The identity
$-\alpha\log|w/2|=-\alpha\log|w|+\alpha\log2$ proves the
last assertion.
\end{proof}

Let $E_r^f(z;M)$ be the event obtained from
$E_1\cap E_2\cap E_3$ by applying $w\mapsto z+rw$ to
every set. It is measurable with respect to
$f|_{B_{7r}(z)}$ modulo constants. The coordinate-change formulas
and invariance under constants give
\[
 1_{E_{2^{-n}}^{h^\alpha}(0;M)}
 =1_{E_1^{\,\mathcal T^n h^\alpha}(0;M)}.
\]
Here the subscript $1$ on $E_r$ denotes radius, not the first
of the three component events.
Put $p_\alpha(M)=\Pp[E_1^{h^\alpha}(0;M)]>0$.
The pointwise ergodic theorem states that for an ergodic
probability-preserving transformation and $F\in L^1$,
$N^{-1}\sum_{n=1}^N F\circ\mathcal T^n\to\E F$ almost surely.
This is Walters, \emph{An Introduction to Ergodic Theory},
Theorem 1.14, p.~34, applied to the indicator of this event.
Consequently
\begin{equation}\label{eq:dyadic-frequency}
 \frac1N\sum_{n=N+1}^{2N}
 1_{E_{2^{-n}}^{h^\alpha}(0;M)}
 =2\frac1{2N}\sum_{n=1}^{2N}1_{E_{2^{-n}}}
       -\frac1N\sum_{n=1}^{N}1_{E_{2^{-n}}}
 \longrightarrow p_\alpha(M)\quad\hbox{almost surely}.
\end{equation}
In particular the count is at least $p_\alpha(M)N/2$
eventually. No independence of the scale events, annular
locality of $\widehat G$, or unspecified GFF tail-triviality
claim is used here.

\section{Transfer to quantum-typical points}
\begin{theorem}[The source's Lemma \texttt{mu\_h-pinch-bad}]
\label{thm:density}
Fix the geometry and $\gamma$, and let
$h=g-\alpha_0\log|\cdot|$ for any fixed $\alpha_0<Q$.
For every $M>0$ there is a deterministic
$\delta_M\in(0,1)$ such that almost surely, for
$\mu_h$-almost every $z\in\C$, for every sufficiently large
$N=N(z,h)$,
\[
 \#\{n\in[N+1,2N]\cap\mathbb Z:
               \widehat G_{2^{-n}}^h(z;M)\}\ge\delta_M N.
\]
One may use $\delta_M=p_\gamma(M)/2$; thus the constant is
independent of $z,N,\alpha_0$, for fixed geometry and $\gamma$.
No positive bound uniform over all $M$ is asserted.
\end{theorem}
\begin{proof}
We use the following precise rooted-field statement.
Duplantier--Miller--Sheffield, arXiv:1409.7055v4,
Lemma A.10, p.~184, in its whole-plane case, identifies the
measure $\Pp(dg)\mu_g(dz)$ on $z\in B_1$, modulo constants:
sample $z$ from Lebesgue measure independently of an unweighted
whole-plane GFF and replace the field by
\begin{equation}\label{eq:rooted-field}
 g^{[z]}(w)=g(w)-\gamma\log|w-z|
                         +\gamma\log\max\{1,|w|\}.
\end{equation}
An additive constant restores the normalization if desired.
This is a finite measure of total mass $\pi$; normalizing it
does not change null sets. Its marked-point formulation follows
from the same Gaussian change of measure: at regularization
scale $\epsilon$, weighting by
$\epsilon^{\gamma^2/2}e^{\gamma g_\epsilon(z)}\,d^2z$
shifts the field by
$\gamma\operatorname{Cov}(g(\cdot),g_\epsilon(z))$.
The root density tends to $1$ on $B_1$, and the shift tends,
modulo constants, to \eqref{eq:rooted-field}.
The subcritical chaos limit gives the marked identity first
for bounded cylinder functions and then for all nonnegative
measurable functions by the monotone-class theorem. This is
also the proof of the quoted lemma.

For a fixed $z\in B_1\setminus\{0\}$ choose a small disk
$B_b(z)$ avoiding $0$ and $\partial B_1$. On this disk,
the field
$g^{[z]}-\alpha_0\log|\cdot|$ is a whole-plane GFF plus
$-\gamma\log|\cdot-z|$ plus a deterministic smooth function.
Cut the latter off outside a slightly larger disk.
Formula \eqref{eq:CM-C} implies that its local law modulo
constants is equivalent to that of a translated
$\gamma$-log-singularity field. Thus the almost-sure frequency
conclusion \eqref{eq:dyadic-frequency} with $\alpha=\gamma$
holds for the events $E_{2^{-n}}(z;M)$ for this rooted field.
The required inequality $\gamma<Q$ holds because $\gamma<2$.
This is a legitimate local transfer: for all large $n$ the
certificates use only $B_{7\cdot2^{-n}}(z)\subset B_b(z)$,
and deleting finitely many terms does not change their
limiting frequency.

Fubini and the marked identity show
\[
 \E\int_{B_1}
 1_{\{\text{certificate frequency fails for }
              g-\alpha_0\log|\cdot|\text{ at }z\}}\,\mu_g(dz)=0.
\]
Hence almost surely failure occurs at no more than a
$\mu_g$-null set of points in $B_1$.
Since
$\mu_h=|\cdot|^{-\gamma\alpha_0}\mu_g$ and neither measure
has an atom at $0$, the same null-set statement holds for
$\mu_h$. The inclusion $E_r^h(z;M)\subset\widehat G_r^h(z;M)$
gives the asserted lower bound.

Apply this argument after deterministic dilation by
$R=2^k$, $k=1,2,\ldots$. The field
$g(R\,\cdot)-g_R(0)$ has the same law as $g$, and the
logarithmic drift, measure and events transform by the stated
coordinate formulas and an irrelevant constant.
The radii in the original coordinates are then
$R2^{-n}=2^{-(n-k)}$. Shifting the index window
$[N+1,2N]$ by the fixed integer $k$ changes its count by
at most $2k$, which disappears after division by $N$.
Thus the same limiting frequency holds at the original
dyadic radii. This proves the result on $B_{2^k}$ and hence on all of $\C$
by a countable intersection. The threshold in $N$ can depend
on the point and environment; the density constant cannot.
If a simultaneous statement for every $M>0$ is wanted, first
intersect the probability-one statements for positive integer
$M$, and use monotonicity with $\lceil M\rceil$.
\end{proof}

\section{The deterministic obstruction to metric balls}
\begin{lemma}\label{lem:obstruction}
Suppose the two metric inequalities in \eqref{eq:hatG} hold
with a length metric $D$ inducing the Euclidean topology. If
$c\notin B_{10r}(z)$ and
$D(c,z)=u>0$, then
\[
       Q'_r(z)\subset\{x:D(c,x)>u\},\qquad
       T_r(z)\subset\{x:D(c,x)<u\}.
\]
\end{lemma}
\begin{proof}
Put
$L=D(Q'_r(z),\partial Q_r(z))$,
$A=\sup_{x\in\partial B_{5r}(z)}D(z,x)$, and
$b=D(z,\partial B_{5r}(z))$.
The event says $L>A$ and $\diam_D(T_r(z))<b$.
Fix $q\in Q'_r(z)$ and a path from $c$ to $q$.
It visits $\partial B_{5r}(z)$ at a point $x$ before entering
$Q_r(z)$. Its length is at least $D(c,x)+L$, by the
first-crossing decomposition. The triangle inequality gives
$D(c,x)\ge u-D(z,x)\ge u-A$. Taking the infimum over
paths proves $D(c,q)\ge u+L-A>u$.

For $t\in T_r(z)$ choose a path from $c$ to $z$ of length
less than $u+\epsilon$ and a visit $x$ to
$\partial B_{5r}(z)$. Its final subpath has length at least
$b$, so its initial subpath has length at most
$u+\epsilon-b$. Because $x\in\overline{T_r(z)}$,
continuity gives
$D(x,t)\le\diam_D(T_r(z))$.
Thus
$D(c,t)\le u+\epsilon-b+\diam_D(T_r(z))<u$
for sufficiently small $\epsilon>0$.
The argument uses nearly shortest paths and therefore does
not require a separate geodesic-existence assumption.
\end{proof}
This proves the source's geometric-event lemma, and also
extends its center $0$ to \emph{every} center $c$ on the same
event. The extension is needed if the proposition allows
arbitrary metric-ball centers.

We now state explicitly the harmonic-ball input.
The source's harmonic comparison lemma
(\texttt{lemma:harmonic-comparison-chain}) says that
there is a deterministic $C_H>0$ such that, simultaneously
in $t,z,r$ with $0\notin\overline B_{10r}(z)$,
\begin{equation}\label{eq:HB-constraint}
 \A_{4r,5r}(z)\cap\Lambda_t^c\ne\varnothing
 \quad\Longrightarrow\quad
 \mu_h(\A_{r,2r}(z)\cap\Lambda_t)\le C_H S_h(r,z).
\end{equation}
Here $\Lambda_t$ denotes the harmonic ball centered at the
source $0$. This is Lemma 11.6, p.~50, of
arXiv:2208.11795v1. Its two precise preceding inputs are
Lemma 6.8, p.~25 (annular mass is bounded by a constant times
the supremum of the odometer on a larger annulus) and
Lemma 6.10, p.~27 (that supremum is bounded by the annular
Green potential if the cluster misses a point of the middle
annulus). To recall the deduction, choose a containing disk
for $\Lambda_t$ and its nonnegative odometer $v_t$.
Those two estimates, and subharmonicity away from $0$, give
\[
 \mu_h(\A_{r,2r}(z)\cap\Lambda_t)
 \le C\sup_{\A_{r/2,4r}(z)}v_t
 \le C\sup_{\partial B_{4r}(z)}v_t
 \le C_H S_h(r,z).
\]
The middle step applies the maximum principle on $B_{4r}(z)$;
the last uses radii $(3,4,5,6)r$ and the missed point.
These are established deterministic obstacle estimates, with
no use of the pinch event or its positive probability.

Take the probability-one event in Theorem~\ref{thm:density}
with $M=C_H$, together with \eqref{eq:HB-constraint}.
Let $z\ne0$ be one of its good points. For any metric ball
$\mathcal B=\{x:D_h(c,x)<u\}$ with
$z\in\partial\mathcal B$, continuity implies $D_h(c,z)=u$,
and $c\ne z$. There are arbitrarily small successful scales;
choose one with
$10r<\min\{|z|,|z-c|\}$.
Lemma~\ref{lem:obstruction} implies
$U_r(z)\subset T_r(z)\subset\mathcal B$ and
$Q'_r(z)\subset\mathcal B^c$. Therefore
\[
 \mu_h(\A_{r,2r}(z)\cap\mathcal B)
 \ge\mu_h(U_r(z))>C_H S_h(r,z).
\]
Since $Q'_r(z)\subset\A_{4r,5r}(z)$, this contradicts
\eqref{eq:HB-constraint} if $\mathcal B=\Lambda_t$, for
\emph{any} $t>0$. We have proved, simultaneously for all
centers and radii, that for $\mu_h$-almost every $z$ no
harmonic ball can be a metric ball with $z$ on its boundary.

\section{From almost every point to almost every time}
We complete the non-metric-ball proposition by deriving
the exact identity for boundary unions over
arbitrary Lebesgue measurable sets of times.
The already established harmonic-ball construction
gives increasing bounded open sets $\Lambda_t$, with
$\mu_h(\Lambda_t)=t$, $\mu_h(\partial\Lambda_t)=0$, and
Hausdorff-continuous closures. These are the properties in
Theorem 1.1, p.~3, and Theorem 5.5, p.~16, of
arXiv:2208.11795v1.

For a fixed realization define the arrival time
\[
 a(x)=\inf\{t>0:x\in\Lambda_t\}\in[0,\infty].
\]
It is measurable, since $\{a<t\}=\bigcup_{s<t,\ s\in\mathbb Q}\Lambda_s$.
Monotonicity and continuity of the masses give
\[
 \mu_h(\{a<t\})=t,\qquad
 \mu_h(\{a\le t\})=t,\qquad t>0.
\]
For the second equality use
$\{a\le t\}=\bigcap_{s>t,\ s\in\mathbb Q}\Lambda_s$ and
continuity from above inside a fixed finite-mass $\Lambda_{t+1}$.
Thus the image of $\mu_h|_{\{0<a<\infty\}}$ under $a$ is
Lebesgue measure on $(0,\infty)$, and every finite level set
of $a$ has zero mass.

For almost every $x$ with $0<a(x)<\infty$,
\begin{equation}\label{eq:arrival-boundary}
                     x\in\partial\Lambda_{a(x)}.
\end{equation}
First, $x$ belongs to $\Lambda_s$ for every $s>a(x)$;
right Hausdorff continuity gives
$x\in\overline{\Lambda_{a(x)}}$.
If $x\in\Lambda_{a(x)}$, choose a rational Euclidean ball
$B$ containing $x$ with $\overline B\subset\Lambda_{a(x)}$.
Put $t_B=\inf\{t:B\subset\Lambda_t\}$. Since $x\notin\Lambda_s$
for $s<a(x)$, we have $t_B=a(x)$.
There are only countably many such balls $B$, and the level
sets $\{a=t_B\}$ have zero mass. This proves
\eqref{eq:arrival-boundary} outside a null set.

There is in fact a single null set outside which each point
belongs to the boundary at exactly its arrival time, if that
time is positive and finite, and at no other time.
To see this, enlarge the exceptional set just constructed by
\[
             \bigcup_{q\in\mathbb Q,\ q>0}\partial\Lambda_q.
\]
Call the resulting null set $N_0$.
Suppose $x\notin N_0$ and $x\in\partial\Lambda_t$.
If $t<a(x)$, choose a rational $q$ strictly between them,
or any rational $q>t$ if $a(x)=\infty$.
Monotonicity gives
$x\in\overline{\Lambda_t}\subset\overline{\Lambda_q}$,
whereas $q<a(x)$ gives $x\notin\Lambda_q$.
This puts $x$ on $\partial\Lambda_q$, a contradiction.
If $t>a(x)$, then $x\in\Lambda_t$, also a contradiction.
Thus $t=a(x)$, and \eqref{eq:arrival-boundary} supplies the
converse when $0<a(x)<\infty$.
In particular, simultaneously for every set
$J\subset(0,\infty)$,
\[
 \left(\bigcup_{t\in J}\partial\Lambda_t\right)
                  \mathbin{\triangle}a^{-1}(J)\subset N_0.
\]
The pushforward identity for $a$ extends from Borel to
Lebesgue measurable sets by completion: a Lebesgue null
set has a Borel null cover whose preimage has zero mass.
The same is therefore true of its preimage.
Consequently, for every Lebesgue measurable $J$, the
boundary union is measurable for the completed $\mu_h$ and
\begin{equation}\label{eq:boundary-union}
       \mu_h\left(\bigcup_{t\in J}\partial\Lambda_t\right)
                         =\Leb(J).
\end{equation}
The exceptional set is independent of $J$, so this applies
pathwise to a set of times selected from the entire realization.

Now let $J$ be the set of times $t$ for which $\Lambda_t$ is
some open $D_h$-ball. This set is Lebesgue measurable.
Here is a precise justification if it is needed: encode an
open set by the values, at rational points, of the Euclidean
distance to its closed complement. For $\Lambda_t$ these
values are monotone functions of $t$. For
$\{D_h(c,\cdot)<u\}$ they are Borel in $(c,u)$, because for
$b>0$ the distance from a fixed $q$ to its complement exceeds
$b$ exactly when
$\max_{x\in\overline B_b(q)}D_h(c,x)<u$.
Equality of the two open sets is therefore a countable
collection of Borel conditions on $(t,c,u)$. Its projection
to $t$ is analytic, hence Lebesgue measurable.

Every point of $\bigcup_{t\in J}\partial\Lambda_t$ is a
boundary point of a harmonic ball which is also a metric
ball. The preceding section puts this entire union in a
single $\mu_h$-null set. Equation~\eqref{eq:boundary-union}
therefore gives
\[
                         \Leb(J)=0.
\]
This is the requested proposition, including arbitrary metric
centers.

\section{Audit of the printed proof and minimal repairs}
The event \eqref{eq:hatG} itself is retained. The necessary
change to the lemma statement is $\widetilde G\mapsto\widehat G$
and an explicit fixed $M>0$. The geometry must be fixed with
the buffer properties implicit in the figure; no randomness
or uniformity over degenerating geometries is intended.
The proof above supplies the following missing details or
repairs.
\begin{enumerate}[label=(\arabic*)]
\item The quantities written $D_h(0,B_\delta)$ in the bump
calculation are zero. They must be distances to
$\partial B_\delta$.
\item The three diameter bounds are for
$T\setminus B_{3\delta}(W)$, $V$, and
$B_{3\delta}(W)\setminus V$. The last set cannot be replaced
by all of $B_{3\delta}(W)$ in the displayed sum.
Its neighborhood must also lie in the plateau of the
shrinking bump.
\item The shrinking factor must be at most
$c_1/(2c_2)$ when the crossing is at least $c_1$ and the
diameter at most $c_2$. The printed reciprocal is wrong.
The bump must explicitly vanish on $U$, so its mass is
preserved. A negative bump only gives
$D_{\rm new}\le D_{\rm old}$; the extra multiplicative
inequality in the printed preservation check does not follow.
\item Strict inequalities require slack. The construction uses
factors $2$ and $1/2$, including in the resampling step.
The printed harmonic correction $\sup_W\varphi$ need not be
finite; conditional equivalence on a compact subdomain
replaces it.
\item Small diameter and large mass are proved together above,
including the two endpoint costs in the triangle inequality.
There is no assumption that multiplying the field by one
positive bump can make mass large and diameter small.
\item The full event uses global upper distances. It cannot
simply be declared measurable with respect to a shrinking
annulus. Our local certificates restrict all upper paths to
$B_7$ and prove locality for the lower exit distances.
\item Positive probability at $\alpha=0$ alone does not justify
the quantum-typical assertion. The construction works also
for $\alpha=\gamma$; dilation ergodicity and the marked
rooted-field identity then prove that assertion.
\item The deterministic obstruction is valid for all metric
centers. The arrival-time argument proves uniqueness of the
boundary time outside a single null set and hence the exact
boundary-union identity for every Lebesgue measurable set of
times, including a set selected from the realization.
\end{enumerate}
Thus both downstream claims follow after these proof repairs.
No polynomial estimate for the frequency error, and no
positive probability uniform over all $M$ or all geometries,
is part of the conclusion.

\begin{thebibliography}{9}
\bibitem{DFGPS}
J.~Dub\'edat, H.~Falconet, E.~Gwynne, J.~Pfeffer, and X.~Sun,
\emph{Weak LQG metrics and Liouville first passage percolation},
\href{https://arxiv.org/pdf/1905.00380v2}{arXiv:1905.00380v2}.
Inputs: Proposition 3.17, p.~43; Lemma 3.19, (3.63), p.~45,
stated explicitly above.
\bibitem{IG4}
J.~Miller and S.~Sheffield,
\emph{Imaginary geometry IV},
\href{https://arxiv.org/pdf/1302.4738v2}{arXiv:1302.4738v2}.
Inputs: Proposition 2.8, pp.~48--49 (conditional Dirichlet-GFF
decomposition); Proposition 2.9, p.~49 (Gaussian shift density).
\bibitem{DMS}
B.~Duplantier, J.~Miller, and S.~Sheffield,
\emph{Liouville quantum gravity as a mating of trees},
\href{https://arxiv.org/pdf/1409.7055v4}{arXiv:1409.7055v4}.
Input: Lemma A.10, p.~184, the whole-plane marked-field
change of measure stated in \eqref{eq:rooted-field}.
\bibitem{Walters}
P.~Walters, \emph{An Introduction to Ergodic Theory},
Graduate Texts in Mathematics 79, Springer, 1982.
\href{https://link.springer.com/book/9780387951522}{Theorem 1.14,
p.~34}: pointwise ergodic averages of an integrable function
converge to its expectation when the transformation is ergodic.
\bibitem{HB}
A.~Bou-Rabee and E.~Gwynne,
\emph{Harmonic balls in Liouville quantum gravity},
\href{https://arxiv.org/pdf/2208.11795v1}{arXiv:2208.11795v1}.
Inputs: Theorem 1.1, p.~3, and Theorem 5.5, p.~16
(monotone continuous mass-parameterized harmonic balls);
the upper volume bound in Lemma 2.4, (2.11), p.~10,
used only at $\alpha_0=0$;
Lemma 11.6, p.~50, the exact implication
\eqref{eq:HB-constraint}, deduced from Lemma 6.8, p.~25,
and Lemma 6.10, p.~27.
The supplied source's target labels are used throughout;
its numbering differs from this older arXiv version.
\end{thebibliography}
\end{document}

```
