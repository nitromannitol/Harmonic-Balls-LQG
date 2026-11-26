# Harmonic balls in Liouville quantum gravity: Lean formalization

A Lean 4 formalization of the numbered results of

> Ahmed Bou-Rabee and Ewain Gwynne, "Harmonic balls in Liouville quantum gravity", arXiv:2208.11795.

[![CI](https://github.com/nitromannitol/Harmonic-Balls-LQG/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Harmonic-Balls-LQG/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Harmonic-Balls-LQG/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Harmonic-Balls-LQG/actions/workflows/comparator.yml)

The statements follow the corrected draft, [`paper/lqg_harmonic_ball-corrected.tex`](paper/lqg_harmonic_ball-corrected.tex). The arXiv source is kept as [`paper/lqg_harmonic_ball.tex`](paper/lqg_harmonic_ball.tex). The corrections to the arXiv source are marked in the corrected draft.

## Content

- `HarmonicBalls/Defs/`: definitions of the Gaussian free field, the Liouville measure and metric, Green functions and harmonic balls.
- `HarmonicBalls/Draft/`: statements of the numbered results, by section of the paper.
- `HarmonicBalls/Proposed/`: literature inputs, each a Prop-valued definition with its published source.
- `HarmonicBalls/Assembly/`: the results of Section 1 (existence, uniqueness and novelty of harmonic balls), assembled from their inputs.
- `HarmonicBalls/Steps/` and `HarmonicBalls/Proofs/`: the reduction of each result to its inputs, and the proofs of the lemmas used, by section.
- `HarmonicBalls/FirstPass/`: the canonical proofs of the numbered results, with the input statements they use; `HarmonicBalls/FirstPass/ClosureAll.lean` imports the counted closure theorems.

## Status

The statements of the numbered results are in `HarmonicBalls/Draft/`. The results depend on the literature inputs only through explicit hypotheses, whose propositions are defined in `HarmonicBalls/Proposed/` and in the input statements of `HarmonicBalls/FirstPass/`. The inputs in `HarmonicBalls/Proposed/` await a check against their published sources.

The counted declaration of each numbered result is listed in [`docs/campaign/COUNTED-MANIFEST.md`](docs/campaign/COUNTED-MANIFEST.md), with the source, binder, definition, consumer and transitive checks of each of its 84 rows (78 numbered results and six definitions). Proposition 2.6 (Kigami 2019, Theorem 13.1) holds with no cited input (`reflectedLBMHeatKernelStmt_holds`, `HarmonicBalls/Proofs/Potential/ReflectedLBMHeatKernelProved.lean`; not yet reviewed, so its binder and transitive checks are open): the input (13.1) of the cited theorem holds almost surely for the LQG measure of every square (`HarmonicBalls/Proofs/Potential/SquareClippedBallVolume.lean`), the scaling from the unit square is proved, the clock of reflected Brownian motion is identified with the additive functional whose Revuz measure is the normalized μ_h (`HarmonicBalls/Proofs/Potential/ReflectedLQGRevuzMeasure.lean`), and the conclusion follows from the cited theorem once the unit-square kernel is shown to be positive (`reflectedLBMHeatKernel_of_kigami_of_positivity`; route in `docs/campaign/audits/ReflectedClockRevuz.md`); every jointly continuous heat kernel of the time change satisfies the Chapman–Kolmogorov identity (`IsLBMHeatKernel.chapmanKolmogorov`, `HarmonicBalls/Proofs/Potential/ReflectedHeatKernelChapmanKolmogorov.lean`); and Proposition 2.6 follows from the cited theorems of Kigami and of Keller–Lenz–Vogt–Wojciechowski alone (`reflectedLBMHeatKernelStmt_of_kigami_of_klvw`, `HarmonicBalls/Proofs/Potential/ReflectedLBMHeatKernelProposition.lean`): the unit-square kernel of the clock of the square is symmetric with respect to ν (`isLBMHeatKernel_symm`, from the occupation identity of the clock from every start, the resolvent identity of the time change and uniqueness of the Laplace transform) and its transition semigroup on `L²(ν)` is irreducible (`isIrreducibleSemigroup_heatKernelL2Semigroup`); and the two instances of these cited theorems that the proof uses are proved (`kigamiLQGInstanceStmt`, `klvwHeatKernelInstanceStmt`): for every additive functional with Revuz measure ν and from every start, the time change has the heat kernel `1 + Σ e^{-t/μ_i} ϕ_i(x) ϕ_i(y)`, from an eigenbasis of the centered Neumann Green operator of the square on `L²(ν)`, which is jointly continuous and strictly positive (`HarmonicBalls/Proofs/Potential/ReflectedEigenHeatKernel.lean`; route in `docs/campaign/audits/ReflectedClockRevuz.md`). Proposition 2.5 holds with a family of LQG clocks that is, for almost every field, a clock from every start, for every 0 < γ < 2 and every insertion α₀ < Q (`HarmonicBalls/Proofs/Potential/LQGClockInsertedEveryStart.lean`); on the same event the clock is, from every start, almost surely continuous and strictly increasing from zero to infinity, with speed measure μ_h (`HarmonicBalls/Proofs/Potential/LQGClockStrictEveryStart.lean`). The corrected Lemma 11.12 holds for every insertion (`HarmonicBalls/FirstPass/Phase2/CorrectedLemma11_12Derived.lean`), and Lemma 11.18 holds as printed for every geometry of concentric disks (`HarmonicBalls/Proofs/Sec11/MassDiamFullField.lean`). Theorem 1.2, Proposition 11.11 and the corrected Lemma 11.13 hold for every `ξ` with no hypothesis (`HarmonicBalls/FirstPass/Phase2/WeylExponentOfDG20.lean`), and also at the canonical exponent (`HarmonicBalls/FirstPass/Phase2/LocalMetricReplacementDerivedCanonical.lean`). The harmonic balls of Theorem 1.1 are the same for the test class with signed Radon measures on `O`, whose support is closed in `O` and whose mass may accumulate at the boundary of `O` (`HarmonicBalls/Proofs/Potential/GreenPotentialClassRelativeSupport.lean`).

Verification: [`checks/AxiomGate.lean`](checks/AxiomGate.lean) prints the axioms of each counted declaration. It is outside the default build; run it with `lake env lean checks/AxiomGate.lean`. It has 390 `#print axioms` lines, and every declaration it prints uses only `propext`, `Classical.choice` and `Quot.sound`; [`docs/campaign/AXIOM-GATE.md`](docs/campaign/AXIOM-GATE.md) records the checks.

## Continuous integration and comparator

**CI** ([`.github/workflows/build.yml`](.github/workflows/build.yml)) builds the library on GitHub-hosted
runners and runs the axiom gate: every one of the 390 reports of `checks/AxiomGate.lean` must list
exactly `propext`, `Classical.choice` and `Quot.sound`. A build from an empty cache is longer than
one hosted job, so it runs in up to five consecutive jobs ([`.github/workflows/build-stage.yml`](.github/workflows/build-stage.yml)),
each resuming the build of the previous one. CI runs on pushes to `main` that change more than
documentation, `paper/`, `docs/`, `notes/` or `archive/`, and on manual dispatch.

**Comparator audit** ([`.github/workflows/comparator.yml`](.github/workflows/comparator.yml), after each successful CI run on `main` (on the commit that CI built) and on manual dispatch) runs [leanprover/comparator](https://github.com/leanprover/comparator) on the pair
[`HarmonicBallsAudit/Introduction/`](HarmonicBallsAudit/Introduction/): `Challenge.lean` imports the
statement module `HarmonicBalls.Draft.Section1` and states Theorems 1.1 and 1.2 and Proposition 1.3
with their statements in that module, `Solution.lean` proves them from the counted declarations, and
the comparator checks that the statements and their dependency closures agree, that only the three
standard axioms are used, and replays the proofs with the Lean kernel and the independent kernel
nanoda. The challenge is not a mathlib-only restatement: the definitions of `HarmonicBalls/Defs/`
and of Lattice-Probability that the statements use are imported, not restated.

## Building

- Toolchain: `leanprover/lean4:v4.35.0-rc2`, as in [`lean-toolchain`](lean-toolchain), with Mathlib `v4.35.0-rc2`.
- Dependencies, pinned in [`lake-manifest.json`](lake-manifest.json): Mathlib; MarkovProcess (`666cda0`); elliptic_regularity (EllipticRegularityLean, `1e29da0`); Lattice-Probability (`10ba33c474`).

```
lake exe cache get
lake build
```

## Repository layout

```text
HarmonicBalls.lean        Root module
HarmonicBalls/Defs/       Definitions (Gaussian free field, Liouville measure and metric, Green functions, harmonic balls)
HarmonicBalls/Draft/      Statements of the numbered results, by section
HarmonicBalls/Proposed/   Literature inputs as Prop-valued definitions, with their published sources
HarmonicBalls/Assembly/   Section 1 results assembled from their inputs
HarmonicBalls/Steps/      Reduction of each result to its inputs, by section
HarmonicBalls/Proofs/     Proofs of the lemmas used by the reductions, by section
HarmonicBalls/FirstPass/  Canonical proofs and the input statements they use (ClosureAll.lean imports the counted closure theorems)
HarmonicBalls/LPStage/    General lemmas staged for Lattice-Probability
HarmonicBalls/Audit/      Checks of the inputs and exports of the results
checks/                   Axiom gate, outside the default build
HarmonicBallsAudit/       Comparator pair of the results of Section 1, outside the default build
docs/                     Inventories, corrections and notes on the formalization
paper/                    Corrected draft, arXiv source, figures
archive/                  Files moved out of the build (see docs/campaign/ARCHIVE.md)
```

## How this was built

The development used AI-assisted proof writing under human direction.

## Authors and citation

The Lean formalization is by Ahmed Bou-Rabee. The paper is by Ahmed Bou-Rabee and Ewain Gwynne.

```bibtex
@misc{bou-rabee-gwynne-harmonic-balls,
  author = {Ahmed Bou-Rabee and Ewain Gwynne},
  title = {Harmonic balls in Liouville quantum gravity},
  eprint = {2208.11795},
  archivePrefix = {arXiv}
}
```

## License

Copyright 2026 Ahmed Bou-Rabee. Licensed under the Apache License, Version 2.0; see [LICENSE](LICENSE).

## Acknowledgements

The Lattice-Probability dependency contains an "LQG, GFF and mated-CRT library adapted from Leonardo Bonanno's lean-formalizations".
