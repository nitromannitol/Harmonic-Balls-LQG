# Finite-source disc correction audit

- Task: `finite-source-whole-plane-disc-correction`; an analytic leaf, not a numbered-result closure.
- `discSourceCorrection` integrates the literal `greatestHarmonicMinorantBall` against the source. `integrable_discCorrectionKernel` proves actual Bochner integrability for finite sources concentrated on a compact subset of the disc, at every interior observer.
- `harmonicOnNhd_discSourceCorrection` proves harmonicity throughout the disc. Joint continuity on the disc product and compactness provide the uniform circle bounds and dominated convergence needed by the harmonic integral theorem. The proof uses the potential-theoretic infrastructure of Leonardo Bonanno.
- `greenPotential_univ_eq_ball_add_discSourceCorrection` integrates the off-diagonal point-source identity when both kernels are integrable and the observer is uncharged. It assumes only almost-everywhere concentration in the disc, so covers compact sources.
- `ae_greenPotential_univ_eq_ball_add_discSourceCorrection` supplies actual integrability of both kernels and excludes source atoms for planar-almost every interior observer. It uses the existing disc product bound and logarithmic product bound. No equality at charged diagonal points is claimed.
- Verification: `lc` and `lb` pass; forbidden-token scan is empty; printed axioms are `propext`, `Classical.choice`, and `Quot.sound` only.
