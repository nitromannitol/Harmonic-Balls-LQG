import HarmonicBalls.Steps.Sec11.WholePlaneWeylShift
import HarmonicBalls.FirstPass.Frozen.S11g

/-! # Universe-polymorphic Weyl identities for a shifted whole-plane field

Copy of `ae_wholePlane_weylScaling_shift` (`Steps/Sec11/WholePlaneWeylShift.lean:25`) for a probability space in any
universe. The only change is that the metric axioms are taken from the FROZEN Prop
`LQGMetricSatisfiesAxiomsUnivFrozen` (`FirstPass/Frozen/S11g.lean`) instead of the `Type`-valued Defs field.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

universe u

/-- The original and continuously shifted whole-plane metrics are length metrics and satisfy the zero, forward and
inverse Weyl identities almost surely, on a probability space in any universe. -/
theorem ae_wholePlane_weylScaling_shift_univ
    (hU : LQGMetricSatisfiesAxiomsUnivFrozen.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (f : Ω → ℂ → ℝ) (hf : ∀ ω, Continuous (f ω))
    (hfmeas : ∀ x, Measurable fun ω => f ω x) :
    ∀ᵐ ω ∂P,
      IsEuclideanLengthMetric (𝔇 (hC ω)) ∧
      IsEuclideanLengthMetric (𝔇 (addFunPairing (hC ω) (f ω))) ∧
      (∀ x y, weylScaling (𝔇 (hC ω)) ξ 0 x y = ENNReal.ofReal (𝔇 (hC ω) x y)) ∧
      (∀ x y, ENNReal.ofReal (𝔇 (addFunPairing (hC ω) (f ω)) x y) =
        weylScaling (𝔇 (hC ω)) ξ (f ω) x y) ∧
      (∀ x y, weylScaling (𝔇 (addFunPairing (hC ω) (f ω))) ξ 0 x y =
        ENNReal.ofReal (𝔇 (addFunPairing (hC ω) (f ω)) x y)) ∧
      (∀ x y, ENNReal.ofReal (𝔇 (hC ω) x y) =
        weylScaling (𝔇 (addFunPairing (hC ω) (f ω))) ξ (fun z => -f ω z) x y) := by
  have hzero : ∀ T : (ℂ → ℝ) → ℝ, addFunPairing T (fun _ => 0) = T := by
    intro T
    funext φ
    simp [addFunPairing]
  have hbase := hU γ ξ 𝔇 h𝔇 Ω P hC hcirc (fun _ _ => 0) hgff
    (by intro ω; fun_prop) (by intro x; fun_prop)
  have hshift := hU γ ξ 𝔇 h𝔇 Ω P hC hcirc f hgff hf hfmeas
  filter_upwards [hbase.ae_isEuclideanLengthMetric, hbase.ae_weylScaling,
    hshift.ae_isEuclideanLengthMetric, hshift.ae_weylScaling] with ω hb hw hs hsw
  simp only [hzero] at hb hw
  refine ⟨hb, hs, ?_, ?_, ?_, ?_⟩
  · intro x y
    change weylScaling (𝔇 (hC ω)) ξ (fun _ => 0) x y = _
    simpa only [hzero] using (hw (fun _ => 0) continuous_const x y).symm
  · exact hw (f ω) (hf ω)
  · intro x y
    change weylScaling (𝔇 (addFunPairing (hC ω) (f ω))) ξ (fun _ => 0) x y = _
    simpa only [hzero] using (hsw (fun _ => 0) continuous_const x y).symm
  · intro x y
    simpa only [addFunPairing_neg_cancel] using (hsw (fun z => -f ω z) (hf ω).neg x y)

end HarmonicBalls
