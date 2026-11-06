# E18: joint product gap for the buffered pinch event

Verdict: **open**, including α₀ = 0 at physical ξ. The proposed outer-barrier
repair below isolates a concrete simultaneous-event obligation; it is not a
proof of positivity or a counterexample to the numbered result. Fix the six
sets and δ before choosing γ, ξ, a carrier, α₀ or M. No additional literature
input is proposed here.

## Exact remaining proposition

Use the exact Lean proposition in
`Steps/Sec11/PinchBufferedThresholdSelection.lean:94–102`, the hypothesis
`hA` of `exists_positive_measure_pinch_buffer_parameters`. It asks for
positive **outer measure** of `pinchFirstEvent ∧ pinchSecondEvent ∧ ∃ q b, …`,
with all five conjuncts there, for the same sample. That theorem then selects
one deterministic pair q,b and supplies exactly `hA` in
`Proofs/Sec11/BufferedPinchCanonicalLaw.lean:35–44`. The existential is inside
the positive-outer-measure event; separate almost-sure existence of finite
bounds and positivity of E₁ ∩ E₂ do not imply it.

For diagnosis, write L, C, H for the three quantities displayed there and
B = inf_{w∉B₆} D(0,w), provided the infimum is interpreted for the actual
metric and is positive. On samples with finite L,C and positive B,H, the
samplewise condition is equivalent to

    L < B  and  L*C < B*H.

The reverse direction first chooses b strictly below B with both strict
inequalities still valid, then uses
`Steps/Sec11/PinchBufferCompatibility.lean:34`; the forward direction follows
from q ≤ 1 and b ≤ B. To use this equivalence with `toReal`, prove finiteness
before converting ENNReal values. `PinchMetricBarrier.lean` and the radial
product criterion at `PinchBufferCompatibility.lean:91` provide an alternative
sufficient lower bound for B; neither asserts its joint probability.

The product condition is independent even if L < B: the positive numbers
L=1/2, B=1, C=3, H=1 require q>1/2 and q<1/3. This is an algebraic
counterexample to selecting q from separate positive and finite margins, not
a realization of an LQG metric or a counterexample to E18.

## Outer annulus: what works and what remains

Choose deterministic radii 5 < r₁ < r₂ < r₃ < 6, and a nonnegative smooth
bump supported in the annulus between 5 and 6, equal to 1 on the closed
annulus r₁ ≤ |z| ≤ r₂. For t > 0, Weyl scaling multiplies the length of
any segment contained in that closed annulus by exp(ξt). Every continuous
path from 0 to the complement of B₆ crosses from radius r₁ to radius r₂.
Thus, for a fixed realization and positive annulus crossing distance k,
its shifted exit lower bound is at least exp(ξt)k. This is a lower bound
for the **global** exit distance, because it applies to every path. The
crossing distance is positive by separation of the two compact circles in
the Euclidean-compatible metric. The argument requires ξ > 0.

An upper bound on shifted L can remain independent of t if, before shifting,
one has a finite common bound on obstacle-avoiding paths **inside B_{r₁}**
from 0 to every point of ∂B₅. This is a separate constrained-path obligation:
L as defined uses the unbounded complement of the obstacle, and finiteness of
that L does not give a bound on these B_{r₁}-constrained paths. Similarly,
the upper bound on C must use actual paths in its δ-thickening, which lies
well inside B₅ under the configuration assumptions. H has a positive lower
bound under the nonnegative shift; a path witnessing C in that thickening is
unaffected by the outer bump. Consequently, on a common event with fixed
positive k,h and finite upper bounds ℓ,c, any deterministic t satisfying

    exp(ξt) k > max(ℓ, ℓ*c/h)

would give the two product margins. These bounds alone do not establish E₁
and E₂ after the shift. In particular, the outer bump changes μ on the
annulus A_{3,6}, hence the Green-potential term of E₂. If 0 ≤ bump ≤ 1,
μ_t ≤ exp(γt) μ for γ > 0, so a valid pre-shift mass condition is the
strict inequality `μ(U) > M * exp(γt) * potential(μ)`, when M ≥ 0 and the
potential is finite. The bump leaves U unchanged. This is a useful
sufficient margin, but t depends on k,h,ℓ,c, and choosing these bounds after
obtaining E₂(M) creates a circular selection. For M < 0 this displayed
comparison needs separate sign handling; it cannot be substituted verbatim.

A precise route still requiring proof is therefore: for one fixed geometry
and each permitted γ and M, find deterministic k,h,ℓ,c,t > 0 satisfying
the displayed inequality and a single positive-outer-measure event on which
(a) the required constrained path and annulus-crossing bounds hold, (b) E₁
survives the bump, and (c) the *strengthened* E₂ mass and diameter margins
hold for that already chosen t. Then verify smooth-shift absolute continuity
for the joint metric/measure observable and the pointwise Weyl bounds.
Alternatively prove the exact existential `hA` directly. No marginal theorem
cited below provides this joint assertion. A conditional GFF resampling
argument must also show that all exterior bounds in (a) and E₁ are
measurable with respect to the conditioning σ-field; a global metric is not
local merely because its endpoints lie outside the resampling region.

## Source scope and singular origin

The corrected paper, lines 3256–3279 and 3355–3482, establishes neither the
B₆-constrained path bound nor the displayed product gap. Its Proposition
11.9 ([published paper, §11.2](https://doi.org/10.1112/plms.70018)) gives a
joint small internal diameter / large mass event for nested open domains;
it does not by itself preserve the exterior event and the additional shell
bound. The paper's use of the dyadic-square Lemma 11.10 and conditional GFF
law still needs the domain and conditional-law bridge described in
`E18PinchSourceCheck.md`. Theorem 1.8 of
[Dubédat–Falconet–Gwynne–Pfeffer–Sun](https://link.springer.com/article/10.1007/s00440-020-00979-6)
gives internal-diameter moments for compact connected sets, not this joint
event. Both references concern the physical LQG parameter regime.

For α₀ = γ, and more generally each α₀ < Q, one additionally needs joint
control of the singular metric at the endpoint 0, including positive inner
radial gaps, finite constrained paths starting at 0 and the coupling of the
singular metric and singular measure under the shifts. Local absolute
continuity away from 0 alone does not give these. The geometry must remain
fixed across α₀; constants and the probability may depend on α₀ and M.
The frozen statement also quantifies ξ without the positive physical-ξ
hypothesis used above; the staged axioms must imply the needed restriction,
or that binder requires a separate argument. No special case here closes the
frozen result, and no claim is made that it is false.
