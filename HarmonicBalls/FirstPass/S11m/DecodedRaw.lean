import HarmonicBalls.FirstPass.S11m.DecodedDomain
import HarmonicBalls.FirstPass.S11n
import HarmonicBalls.Steps.Sec11.PinchLocalData

/-!
# Real form of the decoded metric identity (fp-S11m, owner z4)

Route `notes/fp-gaps/CHATGPT-z4-11-12-local-certificate.md` section 4.3 and section 5 (equation (17)). The punctured-ball
metric decoder `S11ac.metricDecoder_punctured_ball` gives, almost surely, `ENNReal.ofReal (Ψ ℓ p) = ENNReal.ofReal b *
internalMetric D X p.1 p.2` on `X × X`. Since `Ψ` may be negative (only the `ofReal` equality is given), the decoded raw
metric is normalised as `(ENNReal.ofReal (Ψ ℓ (a, b))).toReal`, which is nonnegative. This file converts the identity into
the real form `Dh = b · internalCost D X` required by `decPunct_eq_const_mul_internalMetric`. Deterministic.
-/

namespace HarmonicBalls.S11m

open Set MeasureTheory
open scoped ENNReal

/-- Real form of the decoder identity: if `ofReal (ψ v w) = ofReal b * D(v, w; X)` on `X × X` with `b > 0`, then the
nonnegative normalisation `(ofReal (ψ v w)).toReal` equals `b · internalCost D X v w`. -/
theorem toReal_ofReal_eq_const_mul_internalCost {D ψ : ℂ → ℂ → ℝ} {X : Set ℂ} {b : ℝ} (hb : 0 < b)
    (h : ∀ v ∈ X, ∀ w ∈ X, ENNReal.ofReal (ψ v w) = ENNReal.ofReal b * internalMetric D X v w) :
    ∀ v ∈ X, ∀ w ∈ X, (ENNReal.ofReal (ψ v w)).toReal = b * internalCost D X v w := by
  intro v hv w hw
  unfold internalCost
  rw [h v hv w hw, ENNReal.toReal_mul, ENNReal.toReal_ofReal hb.le]

/-- The annulus Green potential sup of a restricted, rescaled measure (route section 5; the decoded mass `S` of `E₂`).
If the annulus lies in the ball `B` on which the measure decoder is defined, the potential sup of `c • (μ|B)` is
`c · S(μ)`. -/
theorem annulusGreenPotentialSup_smul_restrict {μ : Measure ℂ} {B : Set ℂ} (c : ℝ≥0∞) {z : ℂ} {a b : ℝ}
    (hsub : annulus z a b ⊆ B) :
    annulusGreenPotentialSup (c • μ.restrict B) z a b = c * annulusGreenPotentialSup μ z a b := by
  rw [HarmonicBalls.S11n.annulusGreenPotentialSup_smul]
  congr 1
  exact annulusGreenPotentialSup_eq_of_restrict_eq z a b (by rw [Measure.restrict_restrict_of_subset hsub])

end HarmonicBalls.S11m
