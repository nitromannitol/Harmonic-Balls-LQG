import HarmonicBalls.FirstPass.S11i.Step8Exhaustion
import HarmonicBalls.FirstPass.S11asLocal

/-!
# Per-ball decoders of the unit-ball frequency (Step 8, fp-S11i-hzoom-scale-d, n4)

Building blocks for `Step8UnitBallInputs` (HzoomUnitBall.lean) at `q = qF`, following chat 238 (steps 1-6, 9-11).

* `certificateEvent_of_restrict_scalar_at`: scalar invariance of `CertificateEvent` at an arbitrary centre `z`
  (the centred form of `FirstPassS11asLocal.certificateEvent_of_restrict_scalar`, S11asLocal.lean:96; same proof with `0` replaced by `z`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders

/-- **Scalar invariance of the certificate event at a centre `z`.** If the restricted measures agree up to the
positive factor `a` on `closedBall z (7 r)` and the metrics agree up to the positive factor `b` on the same closed
ball squared, then the two certificate events at `(r, z)` coincide. Centred form of
`FirstPassS11asLocal.certificateEvent_of_restrict_scalar` (S11asLocal.lean:96). -/
theorem certificateEvent_of_restrict_scalar_at (μ μ' : Measure ℂ) (D D' : ℂ → ℂ → ℝ) (Ostar U V W T Q' Q : Set ℂ)
    (η M r : ℝ) (z : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7) (hr : 0 < r)
    (hμ : μ.restrict (closedBall z (7 * r)) = (ENNReal.ofReal a • μ').restrict (closedBall z (7 * r)))
    (hD : Set.EqOn (Function.uncurry D) (Function.uncurry (fun x y => b * D' x y))
      (closedBall z (7 * r) ×ˢ closedBall z (7 * r))) :
    FirstPassS11i.CertificateEvent μ D Ostar U V W T Q' Q η M r z ↔
      FirstPassS11i.CertificateEvent μ' D' Ostar U V W T Q' Q η M r z := by
  refine Iff.trans (FirstPassS11i.certificateEvent_congr_of_eqOn_closedBall (U := U) hC hr hD) ?_
  refine Iff.trans (FirstPassS11aq.certificateEvent_measure_congr (fun x y => b * D' x y) Ostar U V W T Q' Q η M r z
    hr hU hμ) ?_
  exact FirstPassS11asLocal.certificateEvent_smul_iff μ' D' Ostar U V W T Q' Q η M r z ha hb

end HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders

#print axioms HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders.certificateEvent_of_restrict_scalar_at
