import HarmonicBalls.FirstPass.S11aq
import HarmonicBalls.FirstPass.S11i.CertDilate
import HarmonicBalls.FirstPass.S11ah.Cutoff

/-!
# Deterministic covariance of the rooted certificate

The rooted physical pair `(μ, D)` at root `z` is the translate by `-z` of a canonical pair `(ν, E)`; the certificate at
scale `2^{-n}` about `z` of `(μ, D)` is then the certificate of `(ν, E)` at scale `2^{-n}` about `0` (translation,
`FirstPassS11aq.certificateEvent_translate_iff`), and the latter is the certificate of the dilated pair at scale one
(`HarmonicBalls.FirstPassS11iCertDilate.certificateEvent_dilate_iff`). The coordinate-change constants (`a`, `b`) are positive.

This file contains the deterministic core only. The global "identities" version of hCov was removed (its identities are
false as stated: physical and canonical fields agree only on the root's buffered ball); the local version is
`RootedPhysical.lean` (`FirstPassS11ai.rooted_covariance_window`).
-/

namespace FirstPassS11ai

open MeasureTheory Set Metric
open scoped ENNReal

/-- **Deterministic rooted covariance.** For a measure `ν` and metric `E` on the canonical side, the translated pair
`(ν.map (· - (-z)), E (· - z) (· - z))` has the certificate at scale `2^{-n}` about `z` exactly when the dilated pair
`(a • ν.map (· / 2^{-n}), b · E (2^{-n} ·) (2^{-n} ·))` has the certificate at scale one about `0`. -/
theorem certificateEvent_rooted_iff (ν : Measure ℂ) (E : ℂ → ℂ → ℝ) (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (z : ℂ) (n : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    FirstPassS11i.CertificateEvent (ν.map (fun w : ℂ => w - -z)) (fun x y => E (x + -z) (y + -z))
        Ostar U V W T Q' Q η M (FirstPassS11ah.certScale n) z ↔
      FirstPassS11i.CertificateEvent
        (ENNReal.ofReal a • ν.map (fun w : ℂ => w / ((FirstPassS11ah.certScale n : ℝ) : ℂ)))
        (fun u v => b * E (((FirstPassS11ah.certScale n : ℝ) : ℂ) * u) (((FirstPassS11ah.certScale n : ℝ) : ℂ) * v))
        Ostar U V W T Q' Q η M 1 0 := by
  have hR : 0 < FirstPassS11ah.certScale n := by
    unfold FirstPassS11ah.certScale
    positivity
  have h1 := FirstPassS11aq.certificateEvent_translate_iff ν E Ostar U V W T Q' Q η M
    (FirstPassS11ah.certScale n) z (-z)
  have h2 := HarmonicBalls.FirstPassS11iCertDilate.certificateEvent_dilate_iff ν E Ostar U V W T Q' Q η M 1 0 hR ha hb
  rw [add_neg_cancel] at h1
  rw [mul_one, mul_zero] at h2
  exact h1.trans h2.symm

end FirstPassS11ai
