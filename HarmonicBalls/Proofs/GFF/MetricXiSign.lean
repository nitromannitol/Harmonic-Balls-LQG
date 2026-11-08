import HarmonicBalls.Proofs.Sec11.LQGBaseMetricObservable
import HarmonicBalls.Proofs.Sec11.NormalizedBaseMetric
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly
import HarmonicBalls.Proofs.Sec8.ConcentricCircleCovariance
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Fixed distance law and circle fluctuations for the LQG metric

The whole-plane GFF construction used in the intended sign argument is due to
Leonardo Bonanno. These lemmas hold for any realization of that field.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- A fixed evaluation of the base metric has a realization-independent law. -/
theorem IsWholePlaneGFF.identDistrib_baseMetric_value
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc')
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (z w : ℂ) :
    IdentDistrib (fun ω => 𝔇 (hC ω) z w) (fun ω => 𝔇 (hC' ω) z w) P P' := by
  obtain ⟨F, hF, hF_eq⟩ :=
    exists_common_observable_of_distribution_measurable (fun T => 𝔇 T z w)
      (h𝔇.measurable_apply z w)
  have hd := (h.identDistrib_observables_across_spaces h').comp hF
  have heq : (F ∘ fun ω o => o.1.eval (hC ω) (hcirc ω)) =
      (fun ω => 𝔇 (hC ω) z w) := funext fun ω => hF_eq _ _
  have heq' : (F ∘ fun ω o => o.1.eval (hC' ω) (hcirc' ω)) =
      (fun ω => 𝔇 (hC' ω) z w) := funext fun ω => hF_eq _ _
  rw [heq, heq'] at hd
  exact hd

/-- Each normalized affine field gives the same distance law as the original field. -/
theorem IsWholePlaneGFF.identDistrib_normalized_affine_baseMetric_value
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    IdentDistrib (fun ω => 𝔇 (affinePairing hC hcirc (r : ℂ) 0 ω) z w)
      (fun ω => 𝔇 (hC ω) z w) P P := by
  have hg := (wholePlaneGFFAffineInvariance_proved P hC hcirc) h (r : ℂ)
    (by exact_mod_cast hr.ne') 0
  exact hg.identDistrib_baseMetric_value h 𝔇 h𝔇 z w

/-- The circle average at radius `exp (-n)` has second moment `n`. -/
theorem IsWholePlaneGFF.integral_sq_circle_exp_neg_nat
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (n : ℕ) :
    (∫ ω, (hcirc ω (Real.exp (-(n : ℝ))) 0) ^ 2 ∂P) = (n : ℝ) := by
  have heq : (∫ ω, (hcirc ω (Real.exp (-(n : ℝ))) 0) ^ 2 ∂P) =
      ∫ ω, (hcirc ω (Real.exp (-(n : ℝ))) 0 - hcirc ω 1 0) ^ 2 ∂P := by
    apply integral_congr_ae
    filter_upwards [h.ae_circleAverage_one_zero] with ω hω
    rw [hω, sub_zero]
  rw [heq, h.integral_sq_circle_sub_circle (Real.exp_pos _) zero_lt_one]
  simp only [Real.log_exp, Real.log_one, sub_zero, abs_neg, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- The base metric is strictly positive between distinct points almost surely. -/
theorem IsWholePlaneGFF.ae_baseMetric_value_pos
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {z w : ℂ} (hzw : z ≠ w) : ∀ᵐ ω ∂P, 0 < 𝔇 (hC ω) z w := by
  have hm := (h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) h
    (by intro ω; fun_prop) (by intro x; fun_prop)).ae_isEuclideanLengthMetric
  have hzero (T : (ℂ → ℝ) → ℝ) : addFunPairing T (fun _ => 0) = T := by
    funext φ
    simp [addFunPairing]
  simp only [hzero] at hm
  filter_upwards [hm] with ω hmω
  have hn : 0 ≤ 𝔇 (hC ω) z w := by
    have ht := hmω.triangle z w z
    rw [hmω.self_eq_zero, hmω.symm w z] at ht
    linarith
  exact lt_of_le_of_ne hn (Ne.symm (fun he => hzw (hmω.eq_of_eq_zero z w he)))

/-- At exponentially shrinking Euclidean radii, the base distance tends to zero. -/
theorem IsWholePlaneGFF.ae_baseMetric_exp_neg_nat_tendsto_zero
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => 𝔇 (hC ω) 0 (Real.exp (-(n : ℝ)) : ℂ))
      atTop (𝓝 0) := by
  have hm := (h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) h
    (by intro ω; fun_prop) (by intro x; fun_prop)).ae_isEuclideanLengthMetric
  have hzero (T : (ℂ → ℝ) → ℝ) : addFunPairing T (fun _ => 0) = T := by
    funext φ
    simp [addFunPairing]
  simp only [hzero] at hm
  have hr : Tendsto (fun n : ℕ => (Real.exp (-(n : ℝ)) : ℂ)) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
    exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp ht
  filter_upwards [hm] with ω hmω
  have hc := (hmω.continuous_pair.continuousAt (x := (0, 0))).tendsto
  have ht := hc.comp (tendsto_const_nhds.prodMk_nhds hr)
  simpa only [Function.comp_def, hmω.self_eq_zero] using ht

/-- The shrinking base distances also converge to zero in probability. -/
theorem IsWholePlaneGFF.baseMetric_exp_neg_nat_tendstoInMeasure_zero
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    TendstoInMeasure P (fun (n : ℕ) ω => 𝔇 (hC ω) 0 (Real.exp (-(n : ℝ)) : ℂ))
      atTop (fun _ => 0) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact (h.identDistrib_baseMetric_value h 𝔇 h𝔇 0
      (Real.exp (-(n : ℝ)) : ℂ)).aemeasurable_fst.aestronglyMeasurable
  · exact h.ae_baseMetric_exp_neg_nat_tendsto_zero 𝔇 h𝔇

#print axioms IsWholePlaneGFF.baseMetric_exp_neg_nat_tendstoInMeasure_zero

/-- The distance at radius `exp (-n)` in terms of the normalized affine field. -/
theorem IsWholePlaneGFF.ae_baseMetric_exp_neg_nat_eq
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) (n : ℕ) :
    ∀ᵐ ω ∂P,
      𝔇 (hC ω) 0 (Real.exp (-(n : ℝ)) : ℂ) =
        Real.exp (ξ * (hcirc ω (Real.exp (-(n : ℝ))) 0 - lqgQ γ * n)) *
          𝔇 (affinePairing hC hcirc (Real.exp (-(n : ℝ)) : ℂ) 0 ω) 0 1 := by
  have hs := h.ae_normalized_affine_baseMetric
    (wholePlaneGFFAffineInvariance_proved P hC hcirc) 𝔇 h𝔇
    (Real.exp_pos (-(n : ℝ)))
  filter_upwards [hs] with ω hsω
  have hh := hsω 0 1
  simp only [smul_zero, Complex.real_smul, mul_one, Real.log_exp] at hh
  have hh' : 𝔇 (affinePairing hC hcirc (Real.exp (-(n : ℝ)) : ℂ) 0 ω) 0 1 =
      Real.exp (-(ξ * (hcirc ω (Real.exp (-(n : ℝ))) 0 - lqgQ γ * n))) *
        𝔇 (hC ω) 0 (Real.exp (-(n : ℝ)) : ℂ) := by
    convert hh using 1; congr 2; ring
  rw [hh', ← mul_assoc, ← Real.exp_add]
  simp

#print axioms IsWholePlaneGFF.ae_baseMetric_exp_neg_nat_eq
#print axioms IsWholePlaneGFF.ae_baseMetric_value_pos
#print axioms IsWholePlaneGFF.ae_baseMetric_exp_neg_nat_tendsto_zero
#print axioms IsWholePlaneGFF.integral_sq_circle_exp_neg_nat
#print axioms IsWholePlaneGFF.identDistrib_baseMetric_value
#print axioms IsWholePlaneGFF.identDistrib_normalized_affine_baseMetric_value

end HarmonicBalls
