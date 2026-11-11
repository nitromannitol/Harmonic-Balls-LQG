import HarmonicBalls.Draft.Section11
import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstLawTransfer
import HarmonicBalls.Proofs.Sec11.Closure.CorrectedFixedGeometry
import HarmonicBalls.Proofs.GFF.MetricXiSign

/-!
# Lemma 11.15 helpers

Deterministic and parameter-level inputs of `PinchFirstEventPositiveStmt` (`Draft/Section11.lean`, paper
`lemma:first-event-proof`, line 3277):

* `pinchFirstEvent_of_correctedOpenFirstCertificate`: the open corridor certificate (`correctedOpenFirstCertificate`,
  `Proofs/Sec11/CorrectedPinchFirstLawTransfer.lean`) implies the Draft event `pinchFirstEvent`, because the internal
  metric is antitone in the set and `(thickening (2δ) (Q ∪ W))ᶜ ⊇ ball 0 6 \ (closure (thickening (2δ) Q) ∪ closure
  (thickening (2δ) W))`.
* `exists_pinchProofConfiguration`: a configuration `U, V, W, T, Q', Q, δ₀` as required by the `∃` of Lemma 11.15
  (the fixed corrected geometry of `Proofs/Sec11/Closure/CorrectedFixedGeometry.lean`).
* `weylExponent_pos_of_gamma_pos`: `0 < ξ` for an `IsLQGMetric γ ξ 𝔇` with `0 < γ` (`IsLQGMetric.weylExponent_pos`).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- The open corridor certificate implies the Draft first auxiliary event `pinchFirstEvent` (paper Ẽ₁, line 3325). -/
theorem pinchFirstEvent_of_correctedOpenFirstCertificate {D : ℂ → ℂ → ℝ} {W T Q' Q : Set ℂ} {δ : ℝ}
    (h : correctedOpenFirstCertificate D W T Q' Q δ) : pinchFirstEvent D W T Q' Q δ := by
  refine ⟨lt_of_le_of_lt (iSup₂_mono fun y _ => internalMetric_anti D ?_ 0 y) h.1, h.2⟩
  intro x hx hxT
  rw [thickening_union, mem_union] at hxT
  rcases hxT with hQ | hW
  · exact hx.2 (Or.inl (subset_closure hQ))
  · exact hx.2 (Or.inr (subset_closure hW))

/-- A pinch-point proof configuration exists (the fixed corrected geometry). -/
theorem exists_pinchProofConfiguration :
    ∃ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsPinchPointProofConfiguration U V W T Q' Q δ₀ :=
  ⟨_, _, _, _, _, _, _, isCorrectedPinchConfiguration_fixed.toIsPinchPointProofConfiguration⟩

/-- For `0 < γ`, every LQG metric exponent `ξ` is positive (paper eq:xi, `ξ = γ / d_γ > 0`). -/
theorem weylExponent_pos_of_gamma_pos {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hγ : 0 < γ) : 0 < ξ :=
  IsLQGMetric.weylExponent_pos h𝔇 hγ


end HarmonicBalls
