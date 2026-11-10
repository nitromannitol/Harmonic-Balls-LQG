import HarmonicBalls.FirstPass.S11n
import HarmonicBalls.FirstPass.Frozen.S11n

/-!
# Step 15 pull-back with the frozen existence of canonical decoders

Applies the bridge `correctedLemma11_13_of_identification` (`FirstPass/S11n.lean`) to the witnesses that the frozen
input `LQGCanonicalDecodersExistStmt` (`FirstPass/Frozen/S11n.lean`) supplies. The freeze does not name its witnesses, so
the canonical pinch hypothesis is stated for every identification pair; the witness-specific form is
`correctedLemma11_13_of_identification`.
-/

namespace HarmonicBalls.S11n

open MeasureTheory Set Filter
open scoped ENNReal

universe u

/-- Step 15 with the frozen existence (`LQGCanonicalDecodersExistStmt`). The hypothesis `hPinch` is the obligation on
the canonical side: for every identification pair `(Dμ, Dd)`, the canonical pinch statement holds for decoders certified
equal to `(Dμ, Dd)` (`CanonicalDecodersCertified`). -/
theorem correctedLemma11_13_of_existence (hEx : HarmonicBalls.LQGCanonicalDecodersExistStmt.{u})
    {γ ξ α₀ M : ℝ} {U T Q' Q : Set ℂ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hPinch : ∀ (Dμ : CanonSpace → Measure ℂ) (Dd : CanonSpace → ℂ → ℂ → ℝ),
      LQGCanonicalIdentificationStmt.{u} γ ξ α₀ Dμ Dd → ∃ δ ∈ Ioo (0 : ℝ) 1,
        ∃ (Dμ' : CanonSpace → Measure ℂ) (Dd' : CanonSpace → ℂ → ℂ → ℝ),
          CanonicalDecodersCertified.{u} α₀ Dμ Dd Dμ' Dd' ∧ CanonicalPinchConullStmt.{u} α₀ M δ U T Q' Q Dμ' Dd') :
    ∃ δ ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
      ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ᶠ N in atTop,
        δ * N ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard :
          ℝ) := by
  obtain ⟨Dμ, Dd, hId⟩ := hEx γ ξ α₀ hγ0 hγ2 hα
  exact correctedLemma11_13_of_identification hId (hPinch Dμ Dd hId)

end HarmonicBalls.S11n
