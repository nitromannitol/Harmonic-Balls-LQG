import HarmonicBalls.FirstPass.S11j.FieldLevel11_15
import HarmonicBalls.FirstPass.Frozen.S11j

/-!
# First pass, Section 11: the shifted metric in the faithful Lemma 11.15 (fp-S11j, owner n4)

Identification of the Weyl-shifted metric `e^{ξ f} · D_h` with the LQG metric of the shifted field `h + f`, used in the
Cameron-Martin transfer. The metric-level composition is the frozen input `WeylMetricCompositionContinuousOuterFrozen`
(`FirstPass/Frozen/S11j.lean`; replaces the retired, false `WeylMetricCompositionFrozen`, operator note 23:37 UTC). Terminology: Duplantier-Sheffield and Berestycki-Powell
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
inserted LQG metric of the shifted field `h + f`. Inputs: the metric identity of `D_h` (`hD`); the length-metric property
of the unshifted metric `𝔇(h^ℂ)` (`hLen`, axiom I of `IsLQGMetric` at `hC`); the field-level Weyl identity
`WeylScalingCompositionFrozen` (`Frozen/S11d.lean`, for `g = f`); and the metric-level composition
`WeylMetricCompositionContinuousOuterFrozen` (`Frozen/S11j.lean`, operator note 23:37 UTC), applied to the insertion
`-α₀ log|·|` and the continuous shift `f`. -/
theorem ae_shift_metric_eq {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {D : Ω → ℂ → ℂ → ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (hQ1 : WeylMetricCompositionContinuousOuterFrozen) (hFW : WeylScalingCompositionFrozen.{u})
    (hGFF : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ) (hL : IsLQGMetric γ ξ 𝔇)
    (hξ : 0 < ξ)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v)
    (hLen : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)))
    {f : ℂ → ℝ} (hf : Continuous f) :
    ∀ᵐ ω ∂P, (fun x y => (weylScaling (D ω) ξ f x y).toReal) =
      insertedLQGMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f) := by
  have hFW' := hFW γ ξ α₀ Ω P hC hcirc hGFF hγ hγ₂ hα 𝔇 hL f hf
  filter_upwards [hD, hLen, hFW'] with ω hω hLω hFω
  have hD' : D ω = fun x y => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α₀ * Real.log ‖z‖) x y).toReal := by
    funext x y
    obtain ⟨h0, h1⟩ := hω x y
    rw [← h1, ENNReal.toReal_ofReal h0]
  have hfin : ∀ x y, weylScaling (𝔇 (hC ω)) ξ (fun z => -α₀ * Real.log ‖z‖) x y ≠ ⊤ := by
    intro x y
    rw [← (hω x y).2]
    exact ENNReal.ofReal_ne_top
  have hLc : ContinuousOn (fun z : ℂ => -α₀ * Real.log ‖z‖) {z | z ≠ 0} :=
    continuousOn_const.mul (Real.continuousOn_log.comp continuous_norm.continuousOn fun z hz => by simpa using hz)
  have hQ1a := hQ1 ξ hξ (𝔇 (hC ω)) (fun z => -α₀ * Real.log ‖z‖) f hLω hLc hf hfin
  have hc : (fun z : ℂ => -α₀ * Real.log ‖z‖ + f z) = (fun z : ℂ => f z - α₀ * Real.log ‖z‖) :=
    funext fun z => by ring
  rw [hD']
  funext x y
  unfold insertedLQGMetric
  rw [hFω x y, hQ1a x y]
  simp only [hc]

end HarmonicBalls
