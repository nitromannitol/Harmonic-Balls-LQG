import HarmonicBalls.FirstPass.S11h.CoordDistDiam11_17
import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.Proposed.LQG

/-!
# First pass, Lemma 11.17: the metric of the Weyl-shifted pair equals the field metric of the shifted field
(fp-S11h, owner n2)

For a pair `(μ ω, D ω)` and a continuous shift `f`, the Weyl-shifted pair of `weylShiftPair` carries the metric
`u v ↦ (weylScaling (D ω) ξ f u v).toReal`. The field decoders of `CoordDistDiam11_17.lean` are stated for
`fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f)`. This file identifies the two almost surely, for the same metric functional
`𝔇` as the unshifted field: the Weyl identity III of the metric axioms (`LQGMetricFieldAxioms`, Fact 2.2 III,
Proposed/LQG.lean, through the frozen universal form `LQGMetricFieldAxiomsUnivFrozen`) and the composition identity
`WeylScalingCompositionFrozen` (Frozen/S11d.lean) for the shifted field.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

universe u

/-- The metric of the Weyl-shifted pair `weylShiftPair γ ξ f (μ ω, D ω)` is the field metric of the shifted field, almost
surely, for the metric functional `𝔇` of the field: `(weylScaling (D ω) ξ f).toReal = fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f)`
when `D ω = fieldMetric 𝔇 ξ α₀ (hC ω)` almost surely. -/
theorem ae_weylScaling_toReal_eq_fieldMetric_shift
    (hComp : WeylScalingCompositionFrozen.{u}) (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hDae : ∀ᵐ ω ∂P, D ω = fieldMetric 𝔇 ξ α₀ (hC ω)) (f : ℂ → ℝ) (hf : Continuous f) :
    ∀ᵐ ω ∂P, (fun u v => (weylScaling (D ω) ξ f u v).toReal) =
      fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f) := by
  obtain ⟨-, -, hIII, -⟩ := hAx Ω P γ ξ α₀ hC hcirc hGFF hγ0 hγ2 hα 𝔇 h𝔇
  have hcomp := hComp γ ξ α₀ Ω P hC hcirc hGFF hγ0 hγ2 hα 𝔇 h𝔇 f hf
  filter_upwards [hIII, hDae, hcomp] with ω hω hDω hc
  have hDeq : (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) = D ω :=
    hDω.symm
  funext u v
  unfold fieldMetric
  rw [hc u v, hω f hf u v, ← hDeq]

end HarmonicBalls
