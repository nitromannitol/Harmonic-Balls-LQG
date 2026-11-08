# Continuous circle dilation mixing audit

This packet proves the circle-profile part of `l:r10-dilation` in
`~/paper-fleets/hb/notes/sec11-proof/sec11-proof-r10.tex:290`, not the full
joint test-pairing/circle statement or any numbered-result closure.

The carrier is `C(CircleParameter, ℝ)`, with its existing compact-open topology
and Borel sigma-algebra. `continuousCircleDilation` is literally
`continuousCircleAffine` at complex scale `1/2` and center zero. For every
measurable `F` with the fixed-circle almost-everywhere version identities,
the pushforward `P.map F` is invariant, is mixing for all Borel event pairs,
and is ergodic. The existence theorem supplies such a normalized `F` when
`Ω : Type`, using `exists_measurable_continuous_circle_version`.

`continuousCircleDilation_iterate_succ` states the normalized formula at every
positive iterate with scale `(2 : ℝ)⁻¹ ^ n`; the separate zeroth-iterate
identity does not assume arbitrary profiles are normalized. Coordinate
evaluations generate the actual Borel sigma-algebra via Mathlib's
`ContinuousMap.measurableSpace_eq_iSup_comap_eval`. For each fixed iterate,
only finitely many fixed-circle version identities are combined to transfer
the all-observable Gaussian finite-vector factorization. The existing
coordinate-cylinder extension gives event mixing, and the invariant-event
zero-one law gives Mathlib ergodicity.

No raw pairing representation, independent literature premise, or
simultaneous almost-everywhere version identity is introduced. The GFF and
continuous circle-average construction used by the module are due to Leonardo
Bonanno and come through the existing pinned dependencies.

Validation: `lc` and `lb HarmonicBalls.Proofs.GFF.ContinuousCircleDilationMixing`
pass. The raw forbidden-token scan is empty, so the comment-aware scan is also
empty. The printed dependencies of the substantive theorems are only
`propext`, `Classical.choice`, and `Quot.sound`.
