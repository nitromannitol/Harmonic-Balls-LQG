import Mathlib
import HarmonicBalls.FirstPass.S11ah.LocalObsHae
import HarmonicBalls.FirstPass.S11ah.LengthBorelFinal

/-!
# Discharging `hGood` of the almost-sure length property (B1 wiring, owner n3)

`ae_isLengthMetricOn_rootedRefLaw` (`LocalObsHae.lean`) takes the good set of observations as the named
input `hGood`. Ruling chat 236, section 7: `hGood` is the preimage of the Borel set of decoders
`{d | IsLengthMetricOn (ball c₂ r₂) (decoderOn (ball c₂ r₂) d)}` (`measurableSet_isLengthMetricOn_decoderOn`)
under the local decoder `m`, whose measurability `Measurable m` is a conjunct of `LocalMetricReplacementStmt`.
The lemma below is that wiring; it needs no new named input.
-/

open MeasureTheory Set Metric
noncomputable section

namespace HarmonicBalls.FirstPassS11ahLocalObsHaeGood

open HarmonicBalls FirstPassS11ah HarmonicBalls.FirstPassS11ahLengthBorelFinal

/-- The good set `hGood` of `ae_isLengthMetricOn_rootedRefLaw`, from the measurability of the local decoder
`m` (the conjunct `Measurable m` of `LocalMetricReplacementStmt`) and `0 < r₂`. -/
theorem hGood_of_measurable {c₂ : ℂ} {r₂ : ℝ} (hr₂ : 0 < r₂)
    {m : FirstPassS11ahFinite.LocalObs c₂ r₂ →
      ContinuousMap ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)) ℝ} (hm : Measurable m) :
    MeasurableSet {ℓ : FirstPassS11ahFinite.LocalObs c₂ r₂ |
      IsLengthMetricOn (ball c₂ r₂) (decoderOn (ball c₂ r₂) (m ℓ))} :=
  (measurableSet_isLengthMetricOn_decoderOn hr₂).preimage hm

end HarmonicBalls.FirstPassS11ahLocalObsHaeGood
