import HarmonicBalls.Proofs.Sec11.MeasurableCenteredBaseLocality

/-! # Normalized whole-plane LQG metric locality

At zero logarithmic charge the metric of the field is the base metric. The
Section 8 inputs use Leonardo Bonanno's LatticeProb code.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

/-- Normalized internal base metrics have local versions at all sufficiently
small dyadic scales, without assuming samplewise linearity of field pairings. -/
theorem IsWholePlaneGFF.exists_modConst_dyadic_internal_baseMetrics
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
        (∀ᵐ ω ∂P, 0 < c ω) ∧
        (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)]
          (fun ω => G ω x y)) ∧
        (∀ᵐ ω ∂P, ∀ x ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          ∀ y ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          internalMetric (fun x y => c ω * 𝔇 (hC ω) x y)
            (ball 0 (6 * ((2 : ℝ)⁻¹ ^ n))) x y = G ω x y) := by
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => 6 * ((2 : ℝ)⁻¹ ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul 6
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hε))
  refine ⟨K, ?_⟩
  intro n hn
  have hr : 0 < 6 * ((2 : ℝ)⁻¹ ^ n) := by positivity
  obtain ⟨ψ, hψ, hψint⟩ := IsTestFunction.exists_integral_eq_one
    (isOpen_ball : IsOpen (ball (0 : ℂ) (6 * ((2 : ℝ)⁻¹ ^ n)))) ⟨0, mem_ball_self hr⟩
  exact h.exists_modConst_internal_baseMetric_subset 𝔇 h𝔇 isOpen_ball
    (ball_subset_ball (le_of_lt (hK n hn))) ψ hψ hψint

/-- A zero-charge field metric agrees almost surely with its base metric. -/
theorem IsWholePlaneGFF.ae_zeroCharge_metric_eq_base
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ 0 u v) :
    ∀ᵐ ω ∂P, D ω = 𝔇 (hC ω) := by
  have hs := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 h
    (fun _ _ => 0) (fun _ => continuous_const) (fun _ => measurable_const)
  filter_upwards [hD, hs] with ω hD hs
  funext u v
  have hnonneg : 0 ≤ 𝔇 (hC ω) u v := by
    have ht := hs.1.triangle u v u
    rw [hs.1.self_eq_zero, hs.1.symm v u] at ht
    linarith
  have he := congrArg ENNReal.toReal ((hD u v).2.trans (hs.2.2.1 u v))
  simpa only [ENNReal.toReal_ofReal (hD u v).1, ENNReal.toReal_ofReal hnonneg] using he

/-- Zero-charge LQG metrics have normalized dyadic local versions modulo
constants, without a separate singular-metric locality hypothesis. -/
theorem IsWholePlaneGFF.exists_modConst_dyadic_internalMetrics_zeroCharge
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (hD : IsLQGMetricOfField P γ ξ 0 hC D) :
    ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
        (∀ᵐ ω ∂P, 0 < c ω) ∧
        (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst 0 hC (ball 0 ε)]
          (fun ω => G ω x y)) ∧
        (∀ᵐ ω ∂P, ∀ x ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          ∀ y ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          internalMetric (fun x y => c ω * D ω x y)
            (ball 0 (6 * ((2 : ℝ)⁻¹ ^ n))) x y = G ω x y) := by
  obtain ⟨𝔇, h𝔇, hrepr⟩ := hD
  have hrepr' : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ 0 u v := by
    filter_upwards [hrepr] with ω hω u v
    have hf : (fun x : ℂ => -(0 : ℝ) * Real.log ‖x‖) = 0 := by
      funext x
      simp
    simpa only [hf] using hω u v
  have hbase := h.ae_zeroCharge_metric_eq_base 𝔇 h𝔇 hrepr'
  intro ε hε
  obtain ⟨K, hK⟩ := h.exists_modConst_dyadic_internal_baseMetrics (α := 0) 𝔇 h𝔇 ε hε
  refine ⟨K, ?_⟩
  intro n hn
  obtain ⟨c, G, hc, hG, hGeq⟩ := hK n hn
  refine ⟨c, G, hc, hG, ?_⟩
  filter_upwards [hbase, hGeq] with ω hb hg x hx y hy
  rw [hb]
  exact hg x hx y hy

#print axioms IsWholePlaneGFF.exists_modConst_dyadic_internal_baseMetrics
#print axioms IsWholePlaneGFF.ae_zeroCharge_metric_eq_base
#print axioms IsWholePlaneGFF.exists_modConst_dyadic_internalMetrics_zeroCharge

end HarmonicBalls
