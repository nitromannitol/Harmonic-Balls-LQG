# Transposed observer exhaustion

`transposed_green_observer_exhaustion_l1` is a deterministic helper, not a
numbered-result closure. The kernel is `greenFunction V y x`, with source `y`
and observer `x`; the finite source is carried almost everywhere in the bounded
open domain. The observation measure is locally finite and satisfies the stated
local upper-growth condition. The measurable observer sets increase and cover
almost every point for `μ.restrict V`.

The existing finite-source observation integrability result supplies integrable
source slices almost everywhere and an integrable Bochner potential. Its
indicators are precisely the zero extensions of the observer restrictions.
Monotonicity and the almost-everywhere cover give eventual equality with the
full potential. The error is bounded by the integrable norm of that potential,
so dominated convergence yields convergence of its integral to zero. No kernel
symmetry or pointwise assertion at every observer is used.

Lean's axiom print lists only `propext`, `Classical.choice`, and `Quot.sound`.
The potential-theoretic infrastructure uses work of Leonardo Bonanno.
