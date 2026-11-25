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
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "10ba33c47477b94c8a178b8869871b75d32a0c6e"

@[default_target]
lean_lib «HarmonicBalls» where
  globs := #[.andSubmodules `HarmonicBalls]

/-- The comparator pair `HarmonicBallsAudit/Introduction/` (Theorems 1.1, 1.2 and Proposition 1.3).
Not a default target: it builds only on demand (`lake build HarmonicBallsAudit`); the challenge
elaborates with its intentional `sorry`s. -/
lean_lib HarmonicBallsAudit where
  globs := #[.submodules `HarmonicBallsAudit]
