import HarmonicBalls.FirstPass.Frozen.S8c
import LatticeProb.Prob.BirkhoffErgodic

/-!
# Birkhoff's pointwise ergodic theorem, derived from Lattice-Probability

The frozen Prop `BirkhoffPointwiseErgodic` (`HarmonicBalls/FirstPass/Frozen/S8c.lean`) is proved for every universe
from `LatticeProb.ae_tendsto_birkhoffAverage_integral_of_ergodic` (`HarmonicBalls/LPStage/BirkhoffErgodic.lean`).
The frozen statement is not edited here.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology

universe u

/-- **Birkhoff's pointwise ergodic theorem** (the frozen Prop `BirkhoffPointwiseErgodic`), for every universe `u`:
for a probability space `(Y, ν)`, a measure-preserving ergodic `T` and a measurable `f` with `|f| ≤ 1`, the Cesàro
averages of `f` along `T` converge `ν`-almost everywhere to `∫ f ∂ν`. -/
theorem birkhoffPointwiseErgodic_derived : BirkhoffPointwiseErgodic.{u} := by
  intro Y _ ν _ T f hT herg hf hb
  have hfi : Integrable f ν :=
    Integrable.of_bound hf.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)
  exact LatticeProb.ae_tendsto_birkhoffAverage_integral_of_ergodic hT herg hf hfi

end HarmonicBalls
