# Harmonic balls in Liouville quantum gravity: Lean formalization

A Lean 4 formalization of the numbered results of

> Ahmed Bou-Rabee and Ewain Gwynne, "Harmonic balls in Liouville quantum gravity", arXiv:2208.11795.

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

The counted declaration of each numbered result is listed in [`docs/campaign/COUNTED-MANIFEST.md`](docs/campaign/COUNTED-MANIFEST.md), with the source, binder, definition, consumer and transitive checks of each of its 84 rows (78 numbered results and six definitions). Proposition 2.6 (Kigami 2019, Theorem 13.1) has no producer, so its binder and transitive checks are open; the source check of Lemma 11.18 covers a special instance only. Theorem 1.2, Proposition 11.11 and Lemma 11.13 hold for every `ξ` with no hypothesis (`HarmonicBalls/FirstPass/Phase2/WeylExponentOfDG20.lean`), and also at the canonical exponent (`HarmonicBalls/FirstPass/Phase2/LocalMetricReplacementDerivedCanonical.lean`).

Verification: [`checks/AxiomGate.lean`](checks/AxiomGate.lean) prints the axioms of each counted declaration. It is outside the default build; run it with `lake env lean checks/AxiomGate.lean`. It has 267 `#print axioms` lines, and every declaration it prints uses only `propext`, `Classical.choice` and `Quot.sound`; [`docs/campaign/AXIOM-GATE.md`](docs/campaign/AXIOM-GATE.md) records the checks.

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
