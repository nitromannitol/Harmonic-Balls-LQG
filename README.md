# Harmonic balls in Liouville quantum gravity: Lean formalization

This repository is a Lean 4 formalization of the paper A. Bou-Rabee and E. Gwynne, *Harmonic balls in Liouville quantum gravity*, arXiv:2208.11795 ([arXiv](https://arxiv.org/abs/2208.11795)).

## What is formalized and where

- Definitions: `HarmonicBalls/Defs/`.
- Statements of the numbered results: `HarmonicBalls/Draft/`.
- Counted results: `HarmonicBalls/FirstPass/ClosureAll.lean` is the top-level module that imports the closure theorems `closure_N_M` of the first pass.
- Supporting proofs: `HarmonicBalls/FirstPass/`, `HarmonicBalls/Proofs/` and `HarmonicBalls/Steps/`.
- Literature inputs: `HarmonicBalls/Proposed/` and `HarmonicBalls/FirstPass/Frozen/`.

## Status

Every numbered result of the paper is proved in Lean. The results depend on the literature inputs only through explicit hypotheses, whose propositions are defined in `HarmonicBalls/Proposed/` and `HarmonicBalls/FirstPass/Frozen/`. The inputs in `HarmonicBalls/Proposed/` are not yet checked against their published sources. The closure theorems imported by `HarmonicBalls/FirstPass/ClosureAll.lean` use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Corrected paper

The corrected draft of the paper is `paper/lqg_harmonic_ball-corrected.tex`. The arXiv source is kept as `paper/lqg_harmonic_ball.tex`.

## Building

- Toolchain: Lean `v4.35.0-rc2`, as in `lean-toolchain`.
- Dependencies: Mathlib (`v4.35.0-rc2`), Lattice-Probability, MarkovProcess and elliptic_regularity. Their revisions are pinned in `lake-manifest.json`.

To build:

```
lake exe cache get
lake build
```

## AI disclosure

The Lean code was written with AI assistance and checked by Lean.
