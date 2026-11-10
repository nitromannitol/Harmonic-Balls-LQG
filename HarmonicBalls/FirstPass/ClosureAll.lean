import HarmonicBalls.FirstPass.Closure
import HarmonicBalls.FirstPass.Closure.Faithful12
import HarmonicBalls.FirstPass.S2S3S4S9SA.GreenPole
import HarmonicBalls.FirstPass.Closure.Sec8Weyl
import HarmonicBalls.FirstPass.Closure.NoWeylMain
import HarmonicBalls.FirstPass.Closure.Sec11NoWeyl
import HarmonicBalls.FirstPass.Canonical.Stmts
import HarmonicBalls.FirstPass.Canonical.Novelty
import HarmonicBalls.FirstPass.Canonical.NotMetricBall
import HarmonicBalls.FirstPass.Closure.Sec11Canonical
import HarmonicBalls.FirstPass.Closure.Main12Canonical
import HarmonicBalls.FirstPass.Closure.PaperExponent

/-!
# Top-level closure module (fp-closure-all-top-module)

This module imports every numbered closure theorem `closure_N_M` of the first pass:

* the chain of `FirstPass/Closure.lean`, which imports `Closure/Sec6`, `Closure/SecA45`, `Closure/Sec78910`,
  `Closure/Sec11` and `Closure/Bridge12`;
* `closure_1_2_faithful` (`FirstPass/Closure/Faithful12.lean`). `Faithful12.lean` imports `Closure.lean`, so
  `Closure.lean` cannot import it back (import cycle);
* `closure_2_3_withPole` (this file): the closure of Proposition 2.3 with the pole clause, that is
  `GreenFunctionBallWithPoleStmt` (`FirstPass/S2S3S4S9SA/GreenPole.lean`). It is stated here, not in `Closure.lean`,
  so that `Closure.lean` keeps its import list.

This module adds no hypothesis. Its only declaration is `closure_2_3_withPole`.
-/

namespace HarmonicBalls.Closure

/-- Closure of Proposition 2.3 with the pole clause (audit chat 204 §1, operator 09:42 UTC). Unconditional. -/
theorem closure_2_3_withPole : GreenFunctionBallWithPoleStmt := firstPass_2_3_withPole

end HarmonicBalls.Closure
