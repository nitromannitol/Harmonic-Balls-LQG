import HarmonicBalls.Steps.Sec11.WeylLocality
import HarmonicBalls.Proofs.Sec11.ContinuousBackgroundMetricLocality

/-! # Singular metric locality away from the origin

On an open set separated from the origin the logarithmic weight agrees with
a continuous global cutoff. The Section 8 inputs use Leonardo Bonanno's
LatticeProb code. Locality on neighborhoods containing the origin is not
asserted here.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- The normalized internal metric of the logarithmically singular field is
locally measurable modulo constants on open sets at positive distance from the
origin. The singular metric's length property is an explicit assumption. -/
theorem IsWholePlaneGFF.exists_modConst_internal_singularMetric_away_zero
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {U : Set ℂ} (hU : IsOpen U) {r : ℝ} (hr : 0 < r)
    (haway : ∀ z ∈ U, r ≤ ‖z‖)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1) :
    ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
      (∀ᵐ ω ∂P, 0 < c ω) ∧
      (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC U] (fun ω => G ω x y)) ∧
      (∀ᵐ ω ∂P, ∀ x ∈ U, ∀ y ∈ U,
        internalMetric (fun x y => c ω * D ω x y) U x y = G ω x y) := by
  let f : ℂ → ℝ := fun z => -α * Real.log (max ‖z‖ r)
  have hf : Continuous f := by
    apply continuous_const.mul
    apply (continuous_norm.max continuous_const).log
    intro z
    exact ne_of_gt (lt_of_lt_of_le hr (le_max_right _ _))
  have hfg : ∀ z ∈ U, (fun x : ℂ => -α * Real.log ‖x‖) z = f z := by
    intro z hz
    dsimp only [f]
    rw [max_eq_left (haway z hz)]
  obtain ⟨c, G, hc, hG, hGrep⟩ :=
    h.exists_modConst_internal_backgroundMetric (α := α) 𝔇 h𝔇 f hf hU ψ hψ hψint
  have hbase := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 h
    (fun _ => f) (fun _ => hf) (fun _ => measurable_const)
  refine ⟨c, G, hc, hG, ?_⟩
  filter_upwards [hbase, hD, hmetric, hc, hGrep] with ω hb hd hm hcω hg x hx y hy
  have heq : internalMetric (D ω) U x y =
      internalMetric (𝔇 (addFunPairing (hC ω) f)) U x y :=
    hb.1.internalMetric_weylScaling_eq_of_eqOn hm hb.2.1 ξ
      (fun z => -α * Real.log ‖z‖) f (fun u v => (hd u v).2) hb.2.2.2.1 hU hfg x y
  rw [internalMetric_const_mul _ hcω, heq, ← internalMetric_const_mul _ hcω]
  exact hg x hx y hy

#print axioms IsWholePlaneGFF.exists_modConst_internal_singularMetric_away_zero

end HarmonicBalls
