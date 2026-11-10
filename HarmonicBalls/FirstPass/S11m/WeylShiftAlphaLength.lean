import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.FirstPass.Frozen.S11m
import HarmonicBalls.FirstPass.S11m.WeylLengthCompact

/-!
# The α-metric Weyl-shift length property is derived (fp-S11m, owner z4)

The frozen Prop `LQGMetricAlphaWeylShiftLengthFrozen` (`FirstPass/Frozen/S11m.lean`) follows from the a.s. length-metric
property of the α-metric, which is item I of `LQGMetricFieldAxiomsUnivFrozen` (`FirstPass/Frozen/S11j.lean`), and from the
deterministic theorem `weylScaling_continuous_compactSupport_length` (`FirstPass/S11m/WeylLengthCompact.lean`), applied
inside `filter_upwards` (operator note 02:15 UTC). The only external input is `LQGMetricFieldAxiomsUnivFrozen`.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Filter

/-- The frozen α-metric Weyl-shift length Prop, derived from `LQGMetricFieldAxiomsUnivFrozen` (item I) and the
deterministic Weyl-scaling theorem. -/
theorem lqgMetricAlphaWeylShiftLength_of_axioms (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    LQGMetricAlphaWeylShiftLengthFrozen.{u} := by
  intro γ ξ α 𝔇 hγ hγ2 hα h𝔇 Ω _ P hC hcirc hgff f hf hc
  have hI := ((hAx Ω P γ ξ α hC hcirc hgff hγ hγ2 hα 𝔇 h𝔇).1)
  filter_upwards [hI] with ω hω
  exact (weylScaling_continuous_compactSupport_length _ ξ f hω.2 hf.continuous hc).2

end HarmonicBalls
