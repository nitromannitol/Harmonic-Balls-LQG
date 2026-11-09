import HarmonicBalls.FirstPass.S11.MetricBall
import HarmonicBalls.FirstPass.S11.Geometry
import HarmonicBalls.Proposed.LQG

/-!
# First pass, Section 11 (fp-S11, owner n3)

Each theorem `firstPass_11_<k>` concludes the Draft statement of a numbered result of Section 11
(`HarmonicBalls/Draft/Section11.lean`). Its hypotheses are only Draft statements of other numbered results and
EXTERNAL Props (FIRST-PASS FROZEN Props in `FirstPass/Frozen/S11.lean`, the staged `Proposed/` inputs, the
cited Draft statements).

Status (round 1):
* Lemma 11.14 (`PinchEventMetricBallConsequenceStmt`): `firstPass_11_14`, from the staged input
  `LQGMetricFieldAxioms` (Proposed/LQG.lean; Fact 2.2 I-IV for the field, pending operator source-check).
* Definitions 11.1, 11.3, 11.4 are in `Defs/Geometry.lean` (no theorem; Draft "-").
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

open FirstPassS11

/-- FIRST-PASS, Lemma 11.14 (lemma:geometric-event-consequence, paper line 3264), for the Draft statement
`PinchEventMetricBallConsequenceStmt` (`Draft/Section11.lean:275`). The only input beyond the Draft is the staged
field axioms `LQGMetricFieldAxioms` (Proposed/LQG.lean), used for the length-metric property of `D_h` (Fact 2.2 I)
and the Weyl-scaling identity of the metric. -/
theorem firstPass_11_14.{u} (hAx : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    PinchEventMetricBallConsequenceStmt.{u} := by
  intro U T Q' Q hc γ α₀ ξ hγ hγ₂ hα Ω _ P hC hcirc μ D hg hm hd
  obtain ⟨𝔇, h𝔇, hae⟩ := hd
  have hax := hAx Ω P γ ξ α₀ hC hcirc hg hγ hγ₂ hα 𝔇 h𝔇
  filter_upwards [hax.1, hae] with ω hωI hωD
  have hDlen : IsEuclideanLengthMetric (D ω) := by
    have hfun : D ω = fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
      funext u v
      obtain ⟨h0, heq⟩ := hωD u v
      rw [← heq, ENNReal.toReal_ofReal h0]
    rw [hfun]
    exact hωI.2
  intro M _ z r hr h0 u hu hev hfr
  obtain ⟨hev1, hev2, -⟩ := hev
  exact metricBall_of_pinch_event hDlen hc hr h0 hu hev1 hev2 hfr

#print axioms firstPass_11_14

end HarmonicBalls
