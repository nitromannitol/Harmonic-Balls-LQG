import HarmonicBalls.FirstPass.S11i.CertDilate
import HarmonicBalls.FirstPass.S11i.CertHcert

/-!
# Window certificates of the dyadic zoom family are physical certificate events (fp-S11i, owner n3)

Step 8 (F-i) of `CHATGPT-n3-Q1-eq34.md` section 5. For the zoom family of `GammaZoomIdentityStmt`
(`Assembly13.lean`), `μk k ω = a • (μ ω).map (· / 2^k)` and `Dk k ω = b D(2^k ·, 2^k ·)`, the window certificate of index
`n` at the centre `w` (`FirstPassS11i.windowCert`, radius `(2⁻¹)^n`) is the physical certificate event of `(μ, D)` at
Euclidean radius `2^k (2⁻¹)^n` about the point `2^k w`. This is `certificateEvent_dilate_iff` with `R = 2^k`,
`r = (2⁻¹)^n`, `z = w`. No external input.
-/

namespace HarmonicBalls.FirstPassS11iCertZoom

open MeasureTheory Metric Set
open scoped ENNReal

open HarmonicBalls FirstPassS11i

/-- The window certificate of index `n` at centre `w` for the dyadic zoom family at scale `2^k` is the physical
certificate event of `(μ, D)` at radius `2^k (2⁻¹)^n` about `2^k w`. -/
theorem windowCert_zoom_iff {Ω : Type*} (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (μk : ℕ → Ω → Measure ℂ) (Dk : ℕ → Ω → ℂ → ℂ → ℝ) (μ : Measure ℂ) (D : ℂ → ℂ → ℝ)
    (k : ℕ) (ω : Ω) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hμ : μk k ω = ENNReal.ofReal a • μ.map (fun x : ℂ => x / (((2 : ℝ) ^ k : ℝ) : ℂ)))
    (hD : ∀ x y : ℂ, Dk k ω x y = b * D ((((2 : ℝ) ^ k : ℝ) : ℂ) * x) ((((2 : ℝ) ^ k : ℝ) : ℂ) * y))
    (n : ℕ) (w : ℂ) :
    FirstPassS11i.windowCert Ostar U V W T Q' Q η M μk Dk k ω n w ↔
      CertificateEvent μ D Ostar U V W T Q' Q η M ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n)
        ((((2 : ℝ) ^ k : ℝ) : ℂ) * w) := by
  have hD' : Dk k ω = fun x y : ℂ => b * D ((((2 : ℝ) ^ k : ℝ) : ℂ) * x) ((((2 : ℝ) ^ k : ℝ) : ℂ) * y) :=
    funext fun x => funext fun y => hD x y
  unfold FirstPassS11i.windowCert
  rw [hμ, hD']
  exact HarmonicBalls.FirstPassS11iCertDilate.certificateEvent_dilate_iff μ D Ostar U V W T Q' Q η M
    ((2 : ℝ)⁻¹ ^ n) w (pow_pos two_pos k) ha hb

end HarmonicBalls.FirstPassS11iCertZoom
