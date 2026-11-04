import HarmonicBalls.Steps.Sec11.WeylBoundaryGap

/-! # Weyl identities for a shifted whole-plane field

The metric axioms give both directions of Weyl scaling and the length-metric
property after any pointwise measurable random continuous shift. This result
concerns the whole-plane field, without a logarithmic singularity.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- Adding a function to a pairing and then its negative recovers the pairing. -/
theorem addFunPairing_neg_cancel (T : (ℂ → ℝ) → ℝ) (f : ℂ → ℝ) :
    addFunPairing (addFunPairing T f) (fun z => -f z) = T := by
  funext φ
  simp only [addFunPairing, neg_mul, integral_neg]
  exact add_sub_cancel_right (T φ) (∫ x, f x * φ x)

/-- The original and continuously shifted whole-plane metrics are length
metrics and satisfy the zero, forward and inverse Weyl identities almost
surely. The random shift may depend on the field. -/
theorem ae_wholePlane_weylScaling_shift
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ : ℝ)
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
  have hbase := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) hgff
    (by intro ω; fun_prop) (by intro x; fun_prop)
  have hshift := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc f hgff hf hfmeas
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

/-- A continuous random shift that vanishes near the two spheres preserves
their whole-plane metric separation almost surely. -/
theorem ae_wholePlane_pinch_sphere_gap_of_weylShift
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ δ R : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (f : Ω → ℂ → ℝ) (hf : ∀ ω, Continuous (f ω))
    (hfmeas : ∀ x, Measurable fun ω => f ω x)
    (hδ : 0 < δ) (hR : 3 * δ < R)
    (hfzero : ∀ ω x, x ∈ ball (0 : ℂ) R → f ω x = 0) :
    ∀ᵐ ω ∂P,
      ENNReal.ofReal (setDist (𝔇 (hC ω)) (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) ≤
      ENNReal.ofReal (setDist (𝔇 (addFunPairing (hC ω) (f ω)))
        (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) := by
  filter_upwards [ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 hgff f hf hfmeas]
    with ω h
  exact ofReal_setDist_pinch_spheres_le_of_inverse_weylScaling h.1 h.2.1
    hδ hR (hfzero ω) h.2.2.2.2.1 h.2.2.2.2.2

end HarmonicBalls
