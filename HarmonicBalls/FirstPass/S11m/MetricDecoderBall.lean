import HarmonicBalls.FirstPass.S11m.MeasureDecoderBall

/-!
# Common metric decoder on a ball containing `0`: the named hypothesis P-d (fp-S11m, owner z4)

Route: `notes/fp-gaps/CHATGPT-z4-11-12-local-certificate.md`, section 4 (steps 4.1-4.4); operator note 00:59 UTC
(P-d is taken as a named hypothesis until the n2 metric decoder lands; the difference is reported).

`LocalMetricDecoderBallZeroStmt` is the metric counterpart of `measureDecoder_ball_zero` (`MeasureDecoderBall.lean`).
It is a NEW paper step (not an external input), so it is kept here as a named `def`, NOT frozen. It is used only as the
hypothesis P-d of `FirstPass/S11m/Corrected11_12.lean` and must be discharged before `PinchLocalCertificateStmt` is proved.

Shape. For every radius `R > 0` and admissible `(γ, ξ)` there is ONE decoder `Ψ`, common to all models, from the
mean-zero pairings on `B_R(0)` to continuous functions on `B_R(0) × B_R(0)`, Borel in the observation, such that for every
insertion `α₀ < Q` and every model `(P, h, D)` with `D = IsLQGMetricOfField`, almost surely `Ψ` of the observation equals
`b · D_h(·,·; B_R(0))` for some random `b > 0` (the internal metric of the whole ball, not of the punctured ball). The
equality is stated in `ℝ≥0∞` after `ENNReal.ofReal`, so it also forces finiteness of the internal metric.

Why a separate statement from n2's §4 (`CHATGPT-n3-B1-B2.md` §4, eqs (16)-(20)):
* n2's §4 gives decoders on disks `D` with `closure U ⊂ D` and `closure D ⊂ B_1 \ {0}` only. The pinch rule needs the
  internal metric of `B_R(0) ∋ 0` (`ball 0 6`, `ball 0 (4δ)`, `pinchOmegaGeom`), which contains the insertion point.
  Route §4.4 (eqs (15)-(16)) recovers the root `0` from the punctured atlas; this root step is not in n2's §4.
* The rooted identity (n2's (20)) is omitted here. It is needed only if the positivity step (route §6) uses the reference
  mixture; this is OPEN and is reported.
* Internalization to the other domains (`thickening δ A`, `pinchOmegaGeom`, `ball 0 6`) is NOT a further decoder: it is
  the countable chain representation `ChainMetric.chainDistance_eq_internalMetric` applied to `Ψ` (measurable without a
  length hypothesis by `ChainBorel.measurable_chainDistance`).
* Input not frozen here: continuity at `0` of the internal metric of `B_R(0)` (DFGPS Prop 3.17, route §4.4). It is part of
  the content of this named statement (`ContinuousOn` clause) and of its root-recovery proof, not a separate hypothesis.

Nothing in this file is proved; the file only fixes the Lean statement of P-d so that the operator can compare it with n2.
-/

noncomputable section

open MeasureTheory Set Metric Filter ProbabilityTheory
open scoped ENNReal

universe u

namespace HarmonicBalls.S11m.MetricDecoderBall

/-- NAMED HYPOTHESIS P-d (route `CHATGPT-z4-11-12-local-certificate.md` section 4; operator note 00:59 UTC). Common
metric decoder for the internal metric of a ball `B_R(0)` containing the insertion point `0`. SUPERSEDED (operator note 01:41 UTC, item 1; not used by any declaration): the metric replacement is n2's `LocalMetricReplacementStmt` (FirstPass/S11r/LocalMetricReplacement.lean), applied on the countably many balls covering `B_R(0) \ {0}`. For all `R > 0` and
admissible `0 < γ < 2`, `0 < ξ`, there is a map `Ψ` from the mean-zero pairings on `B_R(0)` to functions on `ℂ × ℂ`, with
(i) each `Ψ ℓ` continuous on `B_R(0) × B_R(0)`, (ii) each evaluation `ℓ ↦ Ψ ℓ p` measurable, and (iii) for every
insertion `α₀ < Q_γ` and every model, almost surely `Ψ` of the observation is `b · D(·,·; B_R(0))` on `B_R(0)²` for some
random `b > 0`. -/
def LocalMetricDecoderBallZeroStmt : Prop :=
  ∀ (R : ℝ), 0 < R → ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ →
  ∃ Ψ : ModConstTestPairings (ball (0 : ℂ) R) → ℂ × ℂ → ℝ,
    (∀ ℓ, ContinuousOn (Ψ ℓ) (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R)) ∧
    (∀ p : ℂ × ℂ, Measurable fun ℓ => Ψ ℓ p) ∧
    ∀ α₀ : ℝ, α₀ < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α₀ hC D →
      ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ p ∈ ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R,
        ENNReal.ofReal (Ψ (localModConstField α₀ hC (ball (0 : ℂ) R) ω) p) =
          ENNReal.ofReal b * internalMetric (D ω) (ball (0 : ℂ) R) p.1 p.2

end HarmonicBalls.S11m.MetricDecoderBall

end
