# E18: source check of strengthened pinch positivity

Verdict: **open** at both α₀ = 0 and general α₀ < Q, including α₀ = γ.
The paper's displayed argument does not establish the strengthened event; this
is an identification of a missing step, not a counterexample to positivity.
No numbered result or proposed input is certified here.

## Exact target and quantifiers

`Steps/Sec11/InternalPinchScales.lean:20` replaces *both* global upper
bounds in `Draft/Section11.lean:80` by internal distances in B₆: writing
`I_A(x,y) = internalMetric D A x y`, the first bound is
`sup_{x∈∂B₅} I_B₆(0,x) < D(Q',∂Q)` and the second is
`sup_{x,y∈T} I_B₆(x,y) < D(0,∂B₅)`; the Green-potential mass
inequality is unchanged. Lower bounds remain global distances. The target
is **joint** positive outer measure of all three strict inequalities, not
individual positivity. For 11.12, `Draft/Section11.lean:246` chooses one
`U,T,Q',Q` before all γ, ξ, probability spaces and M; the measurable subset
must be pointwise contained in the ordinary event. The conditional consumer
`Audit/Section11PinchMetricFieldConsumer.lean:22,74` supplies that subset
from strengthened outer positivity and staged field axioms, but does not
supply either premise. For 11.13 the common configuration is also chosen
before α₀ < Q and M (`Draft/Section11.lean:259`); positive probability at
α₀ = 0 alone does not prove the singular-origin case or the rooted frequency
statement.

## What the paper gives and the missing compatibility

In the corrected TeX, lines 3256–3279 define E₁, E₂, E₃. E₁ bounds
`L = sup_{x∈∂B₅} I_A(0,x)` by `D(Q',∂Q)`, where
`A = (B_{2δ}(Q ∪ W))ᶜ`, an **unbounded** set. At 3299–3304 the
paper uses `I_A(0,x) ≥ D(0,x)`, sufficient for its global event. Neither
inclusion `A ⊆ B₆` nor an inequality `I_B₆ ≤ I_A` follows: paths
approximating `I_A` may leave B₆. For the second upper bound, the proof at
3305–3320 combines local diameters into a global diameter. The geometry
places the relevant δ-neighborhoods inside B₆, suggesting a constrained
concatenation repair, but the displayed argument does not establish all
needed intersection/concatenation bounds. It also writes the diameter of
`B_{3δ}(W)` where E₃ controls `B_{3δ}(W) \ V` (E45). Thus neither
strengthened inclusion is established by the displayed proof.

A precise sufficient remaining *joint* claim is the `hA` proposition at
`Proofs/Sec11/BufferedPinchCanonicalLaw.lean:35–44`, for one fixed proof
configuration and each permitted field and M: there are deterministic
`b > 0` and `q ∈ (0,1]` such that the intersection of E₁, E₂(M),
`∀ w ∉ B₆, b ≤ D(0,w)`, `L < q b`, and
`q C < H` has positive outer measure, with
`C = diam_D^δ(B_{3δ}(W) \ V)` and
`H = D(∂B_{2δ},∂B_{3δ})`. The constants may depend on the fixed field
parameters and M, but the configuration may not. This is a sufficient
route, not an assertion that this particular auxiliary event is necessary
for the target. With finite L,C and positive b,H, the simultaneous choice
of q is equivalent to `L < b` and `L*C < b*H`
(`Steps/Sec11/PinchBufferCompatibility.lean:17,34`). E₁ ∩ E₂ positivity
plus separate a.s. finiteness does not imply either inequality on a
positive-probability common set. A radial barrier blocks a path that leaves
B₆ only when the competing obstacle-avoiding path bound is smaller; the
same q must also contract C below H. This is the exact unproved product-gap
step, not an independent pair of positive events.

The printed third bump at lines 3466–3482 uses `min(C₂/C₁,1)`, although
`H ≥ C₁` and `C ≤ C₂`; a sufficient strict contraction is, for example,
`min(1,C₁/(2C₂))`. Non-strict estimates at 3435–3446 also do not by
themselves yield the strict E₂ inequalities (E44/E47). Correcting these
algebraic margins alone does not prove the joint product gap above.

## Source scope

The paper's Fact 2.2 sets ξ = γ/dγ (corrected TeX:439–441), and its bump
construction divides by ξ (3355–3358, 3466–3469). The frozen Lean statement
quantifies arbitrary real ξ without `0 < ξ`; `Defs/LQGMetric.lean:167–181`
likewise treats ξ as a parameter. One must either derive the needed ξ
restriction from those exact axioms or prove the required case uniformly;
the physical-ξ source alone does not justify the universal binder. The
paper's α₀ = 0 statement (3136–3138) does not state strengthened positivity
for general α₀. Smooth shifts away from 0 cannot simply erase the logarithmic
singularity at 0, which is an endpoint of the B₆ internal distances. The
whole-plane smooth-shift absolute continuity already proved in the repository
is not a missing literature input; a joint observable transport through the
singular metric, with the exact premises of `BufferedPinchCanonicalLaw`,
remains to be derived or avoided.

The paper invokes its mass/diameter Lemma 11.10 at 3428; its statement
(2979–2985) concerns dyadic squares, whereas the displayed use concerns V
and U. Proposition 11.9 gives a related open-set result; matching its domain
and the conditional zero-boundary field still requires justification. Neither
statement asserts the buffered product-gap event. Its proof uses [Dubédat–Falconet–Gwynne–
Pfeffer–Sun, *Weak LQG metrics and Liouville first passage percolation*,
Theorem 1.8, p. 378](https://link.springer.com/article/10.1007/s00440-020-00979-6),
which gives finite p-moments for the U-internal diameter of a nontrivial
compact connected K ⊂ U, for p < 4dγ/γ², under that paper's field and
metric assumptions. This is not a joint positivity theorem, nor an
arbitrary-ξ or singular-origin theorem. The published [harmonic balls
paper](https://doi.org/10.1112/plms.70018) is the source of the original
construction; the local corrected TeX is the controlling statement source.
The source-check does not admit the moment theorem as a Lean hypothesis.
