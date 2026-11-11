import HarmonicBalls.FirstPass.Frozen.S11g
import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M5a
import HarmonicBalls.FirstPass.LPBridge.M5b
import HarmonicBalls.LPStage.LQGMetricUniv

/-!
# LP-stage bridge for the universe transport of the LQG metric axioms

* `HarmonicBalls.lqgMetricSatisfiesAxiomsUniv_of_lpStage : LQGMetricSatisfiesAxiomsUnivFrozen.{u}` (`FirstPass/Frozen/S11g.lean:31`),
  from the LP theorem `LatticeProb.LQG.lqgMetricSatisfiesAxiomsUniv` (`LPStage/LQGMetricUniv.lean`).
* `HarmonicBalls.lqgMetricLengthUniv_of_lpStage : LQGMetricLengthUnivFrozen.{u}` (`FirstPass/Frozen/S11j.lean:133`),
  from `LatticeProb.LQG.lqgMetricLengthUniv`.

The HB and LP copies of the hypotheses and of the conclusions are equivalent by `isWholePlaneGFF_iff` (`M1.lean`),
`isLQGMetric_iff` and `satisfiesLQGMetricAxioms_iff` (`M5b.lean`) and `isEuclideanLengthMetric_iff` (`M5a.lean`).
Both bridges are binder-free. No counted theorem is changed.
-/

namespace HarmonicBalls

open MeasureTheory Filter
open LPBridge

universe u

/-- `LQGMetricSatisfiesAxiomsUnivFrozen` (`FirstPass/Frozen/S11g.lean:31`) from the LP stage, binder-free. -/
theorem lqgMetricSatisfiesAxiomsUniv_of_lpStage : LQGMetricSatisfiesAxiomsUnivFrozen.{u} := by
  intro γ ξ 𝔇 hLQG Ω _ P hC hcirc f hGFF hf hfm
  have hLP := LatticeProb.LQG.lqgMetricSatisfiesAxiomsUniv.{u} γ ξ 𝔇 ((isLQGMetric_iff γ ξ 𝔇).1 hLQG) Ω P hC hcirc f
    ((isWholePlaneGFF_iff P hC hcirc).1 hGFF) hf hfm
  exact (satisfiesLQGMetricAxioms_iff P γ ξ 𝔇 _).2 hLP

/-- `LQGMetricLengthUnivFrozen` (`FirstPass/Frozen/S11j.lean:133`, inventory row 42) from the LP stage, binder-free. -/
theorem lqgMetricLengthUniv_of_lpStage : LQGMetricLengthUnivFrozen.{u} := by
  intro γ ξ 𝔇 h0 h1 hLQG Ω _ P hC hcirc hGFF
  have hLP := LatticeProb.LQG.lqgMetricLengthUniv.{u} γ ξ 𝔇 h0 h1 ((isLQGMetric_iff γ ξ 𝔇).1 hLQG) Ω P hC hcirc
    ((isWholePlaneGFF_iff P hC hcirc).1 hGFF)
  filter_upwards [hLP] with ω hω
  exact (isEuclideanLengthMetric_iff _).2 hω

end HarmonicBalls
