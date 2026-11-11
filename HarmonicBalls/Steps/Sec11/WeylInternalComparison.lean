import HarmonicBalls.Steps.Sec11.WeylAnnulusBounds
import HarmonicBalls.Steps.Sec11.SingularWeylBumpInverse

/-! # Local two-sided comparison of Weyl-scaled internal metrics

The exponent only needs bounds on the open domain: paths used for ambient
metric distances may leave it, but internal distances admit local comparison.
The singular-field corollary uses staged metric-field axioms.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- Bounds on the Weyl exponent on an open set compare internal metrics in
both directions, provided the shifted metric has the inverse Weyl identity. -/
theorem IsEuclideanLengthMetric.internalMetric_weylScaling_two_sided
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) {ξ L B : ℝ} {f : ℂ → ℝ}
    {U : Set ℂ} (hU : IsOpen U)
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hreverse : ∀ x y, ENNReal.ofReal (D x y) =
      weylScaling E ξ (fun z => -f z) x y)
    (hlower : ∀ z ∈ U, L ≤ ξ * f z)
    (hupper : ∀ z ∈ U, ξ * f z ≤ B) (x y : ℂ) :
    internalMetric E U x y ≤ ENNReal.ofReal (Real.exp B) * internalMetric D U x y ∧
    internalMetric D U x y ≤ ENNReal.ofReal (Real.exp (-L)) * internalMetric E U x y := by
  have hDnonneg (u v : ℂ) : 0 ≤ D u v := by
    have h := hD.triangle u v u
    rw [hD.self_eq_zero, hD.symm v u] at h
    linarith
  have hEnonneg (u v : ℂ) : 0 ≤ E u v := by
    have h := hE.triangle u v u
    rw [hE.self_eq_zero, hE.symm v u] at h
    linarith
  refine ⟨hD.internalMetric_weylScaling_le hE hEnonneg hU
    (hD.weylScaling_zero ξ) hscale hupper x y, ?_⟩
  apply hE.internalMetric_weylScaling_le hD hDnonneg hU
    (hE.weylScaling_zero ξ) hreverse
  intro z hz
  have h := hlower z hz
  linarith

/-- With the staged singular metric-field axioms, the two-sided comparison
holds simultaneously for every continuous compactly supported nonpositive
shift and every choice of local bounds and open domain. -/
theorem ae_singularField_internalMetric_weylScaling_two_sided
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α hC D)
    (hξ : 0 ≤ ξ) :
    ∀ᵐ ω ∂P, ∀ (f : ℂ → ℝ), Continuous f → HasCompactSupport f →
      (∀ z, f z ≤ 0) → ∀ (U : Set ℂ), IsOpen U → ∀ L B : ℝ,
      (∀ z ∈ U, L ≤ ξ * f z) → (∀ z ∈ U, ξ * f z ≤ B) → ∀ x y,
      let E : ℂ → ℂ → ℝ := fun u v => (weylScaling (D ω) ξ f u v).toReal
      internalMetric E U x y ≤ ENNReal.ofReal (Real.exp B) * internalMetric (D ω) U x y ∧
      internalMetric (D ω) U x y ≤ ENNReal.ofReal (Real.exp (-L)) * internalMetric E U x y := by
  filter_upwards [ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
      haxioms hgff hγ hγ₂ hα hD,
    ae_singularField_weylBump_identities_of_metricFieldAxioms P γ ξ α hC hcirc D
      haxioms hgff hγ hγ₂ hα hD hξ,
    ae_singularField_negative_weylScaling_finite P γ ξ α hC hcirc D
      haxioms hgff hγ hγ₂ hα hD hξ] with ω hm hi hfinite
  intro f hf hc hn U hU L B hl hu x y
  exact hm.internalMetric_weylScaling_two_sided (hi f hf hc hn).1 hU
    (fun u v => (hfinite f hn u v).2) (hi f hf hc hn).2.2 hl hu x y


end HarmonicBalls
