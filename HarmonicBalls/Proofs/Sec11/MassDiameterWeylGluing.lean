import HarmonicBalls.Proofs.Sec11.MassDiameterCoreGluing
import HarmonicBalls.Steps.Sec11.WeylAnnulusBounds
import HarmonicBalls.Steps.Sec11.PinchMeasureWeylShift

/-! # Weyl contraction for the mass-diameter construction -/

namespace HarmonicBalls
open MeasureTheory Set Metric
open scoped ENNReal

/-- A nonpositive Weyl shift preserves the tile distance bounds while a
stronger bound on the core neighborhood contracts the core. The selected
tile mass is preserved when the perturbation vanishes on that set. -/
theorem IsEuclideanLengthMetric.mass_and_internalDiam_of_weyl_core_gluing
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hEnonneg : ∀ x y, 0 ≤ E x y)
    {ξ γ B : ℝ} {f : ℂ → ℝ} {μ : Measure ℂ}
    {ι : Type*} {O O₀ K C S : Set ℂ} {H J : ι → Set ℂ}
    {δ : ℝ} {a b ε : ℝ≥0∞}
    (hO : IsOpen O) (hO₀ : IsOpen O₀) (hO₀O : O₀ ⊆ O)
    (hJopen : ∀ i, IsOpen (J i)) (hJO : ∀ i, J i ⊆ O)
    (hC : C ⊆ O) (hbuffer : O ⊆ thickening δ K)
    (hcover : ∀ x ∈ K, x ∈ C ∨ ∃ i, x ∈ H i)
    (hattach : ∀ i, (H i ∩ C).Nonempty)
    (hzero : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hglobal : ∀ z, ξ * f z ≤ 0) (hcoreweight : ∀ z ∈ O₀, ξ * f z ≤ B)
    (htiles : ∀ i, ∀ x ∈ H i, ∀ y ∈ H i, internalMetric D (J i) x y ≤ a)
    (hcore : ∀ x ∈ C, ∀ y ∈ C, internalMetric D O₀ x y ≤ b)
    (hbudget : a + ENNReal.ofReal (Real.exp B) * b + a < ε)
    (hS : MeasurableSet S) (hfS : ∀ z ∈ S, f z = 0) :
    (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (γ * f z)))) S = μ S ∧
      internalDiam E δ K < ε := by
  constructor
  · have h := restrict_withDensity_exp_eq_of_eq_zero μ γ f hS hfS
    have h' := congrArg (fun ν : Measure ℂ => ν S) h
    simpa only [Measure.restrict_apply hS, inter_self] using h'
  · apply hE.internalDiam_lt_of_attached_pieces hEnonneg hO hC hbuffer hcover
      hattach hJO _ _ hbudget
    · intro i x hx y hy
      have h := hD.internalMetric_weylScaling_le hE hEnonneg (hJopen i)
        hzero hscale (fun z _ => hglobal z) x y
      simpa only [Real.exp_zero, ENNReal.ofReal_one, one_mul] using
        h.trans (by simpa using htiles i x hx y hy)
    · intro x hx y hy
      calc
        internalMetric E O x y ≤ internalMetric E O₀ x y := internalMetric_anti E hO₀O x y
        _ ≤ ENNReal.ofReal (Real.exp B) * internalMetric D O₀ x y :=
          hD.internalMetric_weylScaling_le hE hEnonneg hO₀ hzero hscale hcoreweight x y
        _ ≤ ENNReal.ofReal (Real.exp B) * b := by gcongr; exact hcore x hx y hy

end HarmonicBalls
