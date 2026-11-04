import HarmonicBalls.Proofs.Sec11.NormalizedBaseMetric
import HarmonicBalls.Steps.Sec11.SingularWeylAffineScaling

/-! # Normalization of a logarithmically singular LQG metric -/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- The singular metric of the normalized affine field is a positive
multiple of the geometrically dilated original singular metric, provided
length-parametrized base-metric paths spend zero time at the origin. The
affine-invariance hypothesis is staged pending source checking. -/
theorem IsWholePlaneGFF.ae_normalized_affine_singularMetric
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D D' : Ω → C(ℂ × ℂ, ℝ)}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {k : ℝ} (hk : 0 < k)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω (u, v) ∧
      ENNReal.ofReal (D ω (u, v)) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hD' : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D' ω (u, v) ∧
      ENNReal.ofReal (D' ω (u, v)) =
        weylScaling (𝔇 (affinePairing hC hcirc (k : ℂ) 0 ω)) ξ
          (fun x => -α * Real.log ‖x‖) u v)
    (hzero : ∀ᵐ ω ∂P, ∀ T p, IsLengthParametrized (𝔇 (hC ω)) p T →
      ∀ᵐ t ∂(volume.restrict (Icc 0 T)), p t ≠ 0) :
    ∀ᵐ ω ∂P, ∀ u v, D' ω (u, v) =
      (Real.exp (-ξ * (hcirc ω k 0 + lqgQ γ * Real.log k)) *
        Real.exp (ξ * (α * Real.log k))) * D ω (k • u, k • v) := by
  have hbase := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) h
    (by intro ω; fun_prop) (by intro x; fun_prop)
  have hpair : ∀ T : (ℂ → ℝ) → ℝ, addFunPairing T (fun _ => 0) = T := by
    intro T
    funext φ
    simp [addFunPairing]
  filter_upwards [h.ae_normalized_affine_baseMetric hAff 𝔇 h𝔇 hk,
    hbase.ae_isEuclideanLengthMetric, hD, hD', hzero] with ω hn hb hd hd' hz
  simp only [hpair] at hb
  intro u v
  let c := Real.exp (-ξ * (hcirc ω k 0 + lqgQ γ * Real.log k))
  let d := Real.exp (ξ * (α * Real.log k))
  have hc : 0 < c := Real.exp_pos _
  have heq : 𝔇 (affinePairing hC hcirc (k : ℂ) 0 ω) =
      (fun x y => c * 𝔇 (hC ω) (k • x) (k • y)) := by
    funext x y
    exact hn x y
  have hscaled := hb.weylScaling_log_const_mul_comp_real_smul ξ α hk hc hz u v
  rw [← heq, ← (hd' u v).2, ← (hd (k • u) (k • v)).2] at hscaled
  have he : ENNReal.ofReal (D' ω (u, v)) =
      ENNReal.ofReal (c * d * D ω (k • u, k • v)) := by
    rw [ENNReal.ofReal_mul (mul_nonneg hc.le (Real.exp_nonneg _)),
      ENNReal.ofReal_mul hc.le]
    exact hscaled
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_ofReal (hd' u v).1,
    ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hc.le (Real.exp_nonneg _))
      (hd (k • u) (k • v)).1)] at hr
  exact hr

/-- A dilated singular metric with the canonical normalization satisfies the
Weyl representation for the normalized affine field. -/
theorem IsWholePlaneGFF.ae_normalized_affine_singularMetric_representation
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D D' : Ω → C(ℂ × ℂ, ℝ)}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {k : ℝ} (hk : 0 < k)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω (u, v) ∧
      ENNReal.ofReal (D ω (u, v)) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hD' : ∀ᵐ ω ∂P, ∀ u v, D' ω (u, v) =
      (Real.exp (-ξ * (hcirc ω k 0 + lqgQ γ * Real.log k)) *
        Real.exp (ξ * (α * Real.log k))) * D ω (k • u, k • v))
    (hzero : ∀ᵐ ω ∂P, ∀ T p, IsLengthParametrized (𝔇 (hC ω)) p T →
      ∀ᵐ t ∂(volume.restrict (Icc 0 T)), p t ≠ 0) :
    ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D' ω (u, v) ∧
      ENNReal.ofReal (D' ω (u, v)) =
        weylScaling (𝔇 (affinePairing hC hcirc (k : ℂ) 0 ω)) ξ
          (fun x => -α * Real.log ‖x‖) u v := by
  have hbase := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) h
    (by intro ω; fun_prop) (by intro x; fun_prop)
  have hpair : ∀ T : (ℂ → ℝ) → ℝ, addFunPairing T (fun _ => 0) = T := by
    intro T
    funext φ
    simp [addFunPairing]
  filter_upwards [h.ae_normalized_affine_baseMetric hAff 𝔇 h𝔇 hk,
    hbase.ae_isEuclideanLengthMetric, hD, hD', hzero] with ω hn hb hd hd' hz
  simp only [hpair] at hb
  intro u v
  let c := Real.exp (-ξ * (hcirc ω k 0 + lqgQ γ * Real.log k))
  let d := Real.exp (ξ * (α * Real.log k))
  have hc : 0 < c := Real.exp_pos _
  have hdpos : 0 ≤ d := Real.exp_nonneg _
  have heq : 𝔇 (affinePairing hC hcirc (k : ℂ) 0 ω) =
      (fun x y => c * 𝔇 (hC ω) (k • x) (k • y)) := by
    funext x y
    exact hn x y
  have hscaled := hb.weylScaling_log_const_mul_comp_real_smul ξ α hk hc hz u v
  rw [← heq, ← (hd (k • u) (k • v)).2] at hscaled
  rw [hd' u v]
  refine ⟨mul_nonneg (mul_nonneg hc.le hdpos) (hd (k • u) (k • v)).1, ?_⟩
  rw [ENNReal.ofReal_mul (mul_nonneg hc.le hdpos), ENNReal.ofReal_mul hc.le]
  exact hscaled.symm

#print axioms IsWholePlaneGFF.ae_normalized_affine_singularMetric
#print axioms IsWholePlaneGFF.ae_normalized_affine_singularMetric_representation

end HarmonicBalls
