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
import HarmonicBalls.FirstPass.S8dNoWeyl
import HarmonicBalls.FirstPass.Closure.Sec11CanonicalOf13
import HarmonicBalls.FirstPass.Closure.Main12CanonicalOf13
import HarmonicBalls.FirstPass.Closure.PaperExponentOf13
import HarmonicBalls.FirstPass.Closure.C1112Clean
import HarmonicBalls.FirstPass.Closure.LocalRootKernelAc
import HarmonicBalls.FirstPass.S11i.Final11_13Close

/-!
# Top-level closure module

This module imports every numbered closure theorem `closure_N_M`:

* the chain of `FirstPass/Closure.lean`, which imports `Closure/Sec6`, `Closure/SecA45`, `Closure/Sec78910`,
  `Closure/Sec11` and `Closure/Bridge12`;
* `closure_1_2_faithful` (`FirstPass/Closure/Faithful12.lean`). `Faithful12.lean` imports `Closure.lean`, so
  `Closure.lean` cannot import it back (import cycle);
* `closure_2_3_withPole` (this file): the closure of Proposition 2.3 with the pole clause, that is
  `GreenFunctionBallWithPoleStmt` (`FirstPass/S2S3S4S9SA/GreenPole.lean`). It is stated here, not in `Closure.lean`,
  so that `Closure.lean` keeps its import list.
* `firstPass_11_13_closed` (`FirstPass/S11i/Final11_13Close.lean`), the counted Lemma 11.13 with no open binder. Nothing
  in the import closure above reaches it, so this module imports it; it declares nothing here.

This module adds no hypothesis. Its only declaration is `closure_2_3_withPole`.
-/

namespace HarmonicBalls.Closure

/-- Closure of Proposition 2.3 with the pole clause. Unconditional. -/
theorem closure_2_3_withPole : GreenFunctionBallWithPoleStmt := firstPass_2_3_withPole

end HarmonicBalls.Closure
