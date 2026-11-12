import Lake
open Lake DSL

package «harmonic-balls-lqg» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

require MarkovProcess from git
  "https://github.com/scottnarmstrong/MarkovProcess" @ "666cda029098a1106914fc9fa7abd1727573284a"

require elliptic_regularity from git
  "https://github.com/scottnarmstrong/EllipticRegularityLean" @ "1e29da02bcc6e3c2359a5b8e0559e76d02ec4002"

-- The lean-v4.35 line of Lattice-Probability: LQG, GFF and mated-CRT library adapted from Leonardo Bonanno's lean-formalizations.
require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "1b203be38a287baab91a548d466ae74222d7ce3b"

@[default_target]
lean_lib «HarmonicBalls» where
  globs := #[.andSubmodules `HarmonicBalls]
