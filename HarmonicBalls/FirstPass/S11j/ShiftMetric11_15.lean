import HarmonicBalls.FirstPass.S11j.FieldLevel11_15
import HarmonicBalls.FirstPass.Frozen.S11j

/-!
# Section 11: the shifted metric in the faithful Lemma 11.15

Identification of the Weyl-shifted metric `e^{ξ f} · D_h` with the LQG metric of the shifted field `h + f`, used in the
Cameron-Martin transfer. The metric-level composition is the frozen input `WeylMetricCompositionContinuousOuterFrozen`
(`FirstPass/Frozen/S11j.lean`). Terminology: Duplantier-Sheffield and Berestycki-Powell
(Weyl scaling `e^{ξ h} D`, LQG metric), Armitage-Gardiner (internal distance).
-/

namespace HarmonicBalls

universe u

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- The weighted-length infimum depends on `D` only through `ENNReal.ofReal ∘ D`, since the curve length does. -/
theorem curveLength_congr_ofReal {D₁ D₂ : ℂ → ℂ → ℝ}
    (h : ∀ x y, ENNReal.ofReal (D₁ x y) = ENNReal.ofReal (D₂ x y)) (p : ℝ → ℂ) (a b : ℝ) :
    curveLength D₁ p a b = curveLength D₂ p a b := by
  unfold curveLength
  simp only [h]

/-- `weylScaling` depends on the metric only through `ENNReal.ofReal ∘ D`. -/
theorem weylScaling_congr_ofReal {D₁ D₂ : ℂ → ℂ → ℝ}
    (h : ∀ x y, ENNReal.ofReal (D₁ x y) = ENNReal.ofReal (D₂ x y)) (ξ : ℝ) (g : ℂ → ℝ) :
    weylScaling D₁ ξ g = weylScaling D₂ ξ g := by
  have hP : ∀ (p : ℝ → ℂ) (T : ℝ), IsLengthParametrized D₁ p T = IsLengthParametrized D₂ p T := by
    intro p T
    apply propext
    unfold IsLengthParametrized
    simp only [curveLength_congr_ofReal h]
  funext u v
  unfold weylScaling
  refine iInf_congr fun T => iInf_congr fun p => ?_
  rw [hP p T]

/-- Almost surely, the Weyl-shifted metric `e^{ξ f} · D_h` (`ℝ`-valued, `D_h` the metric of the unshifted field) is the
inserted LQG metric of the shifted field `h + f`. Inputs: the metric identity of `D_h` (`hD`); the field-level Weyl
identity `WeylScalingCompositionFrozen` (`Frozen/S11d.lean`, for `g = f`); and clause III (Weyl scaling) of the field
axioms `LQGMetricFieldAxioms` (`Proposed/LQG.lean`) for the continuous shift `f`. No length-metric input and no
`WeylMetricCompositionContinuousOuterFrozen` is used: with `W_s = weylScaling · ξ (-α₀ log|·|)`, a.s. `W_s(𝔇(h^ℂ + f)) = W_{f - α₀ log}(𝔇(h^ℂ))
= W_f(D_h)`, and `toReal` gives the claim. -/
theorem ae_shift_metric_eq {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {D : Ω → ℂ → ℂ → ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (hFW : WeylScalingCompositionFrozen.{u})
    (hGFF : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ) (hL : IsLQGMetric γ ξ 𝔇)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v)
    {f : ℂ → ℝ} (hf : Continuous f) :
    ∀ᵐ ω ∂P, (fun x y => (weylScaling (D ω) ξ f x y).toReal) =
      insertedLQGMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f) := by
  obtain ⟨-, -, hIII, -⟩ := haxioms hGFF hγ hγ₂ hα 𝔇 hL
  have hFW' := hFW γ ξ α₀ Ω P hC hcirc hGFF hγ hγ₂ hα 𝔇 hL f hf
  filter_upwards [hD, hIII, hFW'] with ω hω hIIIω hFω
  have hmetric : (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) = D ω := by
    funext u v
    obtain ⟨h0, h1⟩ := hω u v
    rw [← h1, ENNReal.toReal_ofReal h0]
  have hWf : ∀ u v, weylScaling (𝔇 (hC ω)) ξ (fun x => f x - α₀ * Real.log ‖x‖) u v =
      weylScaling (D ω) ξ f u v := by
    intro u v
    rw [← hmetric]
    exact hIIIω f hf u v
  funext x y
  unfold insertedLQGMetric
  rw [hFω x y, hWf x y]

end HarmonicBalls
