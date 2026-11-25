import HarmonicBalls.FirstPass.Phase2.DerivedInputs43
import HarmonicBalls.FirstPass.Phase2.WeylExponentOfDG20

/-!
# Theorems 1.1 and 1.2 and Proposition 1.3: comparator solution

Proves the three statements of `HarmonicBallsAudit/Introduction/Challenge.lean` from their counted
declarations (`docs/campaign/COUNTED-MANIFEST.md`), none of which takes a hypothesis:
`HarmonicBalls.firstPass_1_1_derivedInputs43` and `HarmonicBalls.Closure.closure_1_3_derivedInputs43`
(`HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean`), and the every-`ξ` form of Theorem 1.2,
`HarmonicBalls.firstPass_1_2_forallXi_derived` (`HarmonicBalls/FirstPass/Phase2/WeylExponentOfDG20.lean`).
-/

universe u

namespace HarmonicBallsAudit.Introduction

/-- **Theorem 1.1**: almost surely, for every `z ∈ ℂ` there is a unique family of LQG harmonic balls
centred at `z` satisfying the conditions of the theorem. -/
theorem existence_uniqueness : HarmonicBalls.ExistenceUniquenessHarmonicBallsStmt.{u} :=
  HarmonicBalls.firstPass_1_1_derivedInputs43.{u}

/-- **Theorem 1.2**: almost surely, for almost every `t`, `Λ_t(0)` is neither a Lipschitz domain nor
an LQG-metric ball (for every LQG metric of the field), and for each `t > 0` the boundaries of the
complementary components of its closure are Jordan curves. -/
theorem novelty : HarmonicBalls.HarmonicBallNoveltyStmt.{u} :=
  HarmonicBalls.firstPass_1_2_forallXi_derived.{u}

/-- **Proposition 1.3**: each closed LQG harmonic ball is a local set of the field. -/
theorem local_set : HarmonicBalls.HarmonicBallLocalSetStmt.{u} :=
  HarmonicBalls.Closure.closure_1_3_derivedInputs43.{u}

end HarmonicBallsAudit.Introduction
