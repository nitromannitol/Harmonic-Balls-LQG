import HarmonicBalls.FirstPass.S11p.ExteriorMass
import HarmonicBalls.Proposed.LQG

/-!
# First pass, Section 11: the second annulus step from the N2 interface (fp-S11t, owner n4)

This file proves `PinchSecondAnnulusStep` exactly as typed in `FirstPass/S11k/BundleParts.lean` (owner z3), from the
N2 interface `exists_exterior_annulusGreenPotentialSup_of_buffered_singular` (`FirstPass/S11p/ExteriorMass.lean`).
The insertion-0 LQG measure `μ₀` on the same space is produced by the Proposed input `LQGMeasureExistence`
(`Proposed/LQG.lean`), not assumed. The statement is copied (not imported) so that `BundleParts` can import this file.

Named hypotheses. The step quantifies over every model, so each model-level input is taken universally:
* frozen: `LQGMassInnerMeasurableFrozen` (`hFr`), `WholePlaneCircleAverageLimitFrozen` (`hBr`);
* cited: `GreenPotentialHolderStmt` (`hholder`, Bou-Rabee-Gwynne Prop 2.5);
* Proposed, pending operator source-check: `LQGMeasureExistence` at insertion 0 (`hEx`), `LQGMeasureWeylScaling` at
  insertion 0 (`hWeyl`), `LQGMeasureNonatomic` at insertion 0 (`hNa0`) and at insertion `α₀` (`hNa`).
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

universe u

namespace PinchSecondAnnulusS11t

/-- The N2 step `PinchSecondAnnulusStep` (`FirstPass/S11k/BundleParts.lean`), proved from the named inputs. -/
theorem pinchSecondAnnulusStep_of_N2_inputs
    (hFr : LQGMassInnerMeasurableFrozen.{u}) (hBr : WholePlaneCircleAverageLimitFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hEx : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hWeyl : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hNa0 : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ 0 hC hcirc)
    (hNa : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    ∀ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∃ G : Ω → ℝ≥0∞,
      Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] G ∧
        (∀ᵐ ω ∂P, G ω = annulusGreenPotentialSup (μ ω) 0 3 6) ∧ ∀ᵐ ω ∂P, G ω ≠ ⊤ := by
  intro U V W T Q' Q δ hG γ α₀ hγ0 hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hQ0 : (0 : ℝ) < lqgQ γ := by
    unfold lqgQ
    have := div_pos two_pos hγ0
    have := div_pos hγ0 two_pos
    linarith
  obtain ⟨μ₀, h₀⟩ := hEx γ Ω P hC hcirc hGFF hγ0 hγ2 hQ0
  exact exists_exterior_annulusGreenPotentialSup_of_buffered_singular hGFF γ α₀ μ μ₀ hγ0 hγ2 hα hμ hFr hBr hholder h₀
    (hWeyl γ Ω P hC hcirc) (hNa0 γ Ω P hC hcirc) (hNa γ α₀ Ω P hC hcirc) hG

end PinchSecondAnnulusS11t

end HarmonicBalls

#print axioms HarmonicBalls.PinchSecondAnnulusS11t.pinchSecondAnnulusStep_of_N2_inputs
