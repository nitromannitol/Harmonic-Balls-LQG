import HarmonicBalls.Draft.Section1

/-!
# Theorems 1.1 and 1.2 and Proposition 1.3: comparator challenge

Comparator challenge for the results of the introduction of A. Bou-Rabee and E. Gwynne,
*Harmonic balls in Liouville quantum gravity*, arXiv:2208.11795, in the corrected draft
`paper/lqg_harmonic_ball-corrected.tex`: the existence and uniqueness of LQG harmonic balls
(Theorem 1.1), their novelty and the Jordan boundaries of their complementary components
(Theorem 1.2), and their locality (Proposition 1.3).

This file imports only the statement module `HarmonicBalls.Draft.Section1` and, through it, the
definitions of `HarmonicBalls/Defs/` (the whole-plane Gaussian free field, the LQG measure and
metric, harmonic balls) and the Mathlib and Lattice-Probability modules they use. Each theorem
below has for its type the statement of the result in `HarmonicBalls/Draft/Section1.lean`, with no
hypothesis beyond those of the printed result; `docs/campaign/COUNTED-MANIFEST.md` records the check
of each statement against the corrected draft. The three proofs are the intentional `sorry`s of this
file; `Solution.lean` proves the same three statements from the library.
-/

universe u

namespace HarmonicBallsAudit.Introduction

/-- **Theorem 1.1**: almost surely, for every `z ∈ ℂ` there is a unique family of LQG harmonic balls
centred at `z` satisfying the conditions of the theorem. -/
theorem existence_uniqueness : HarmonicBalls.ExistenceUniquenessHarmonicBallsStmt.{u} := by
  sorry

/-- **Theorem 1.2**: almost surely, for almost every `t`, `Λ_t(0)` is neither a Lipschitz domain nor
an LQG-metric ball (for every LQG metric of the field), and for each `t > 0` the boundaries of the
complementary components of its closure are Jordan curves. -/
theorem novelty : HarmonicBalls.HarmonicBallNoveltyStmt.{u} := by
  sorry

/-- **Proposition 1.3**: each closed LQG harmonic ball is a local set of the field. -/
theorem local_set : HarmonicBalls.HarmonicBallLocalSetStmt.{u} := by
  sorry

end HarmonicBallsAudit.Introduction
