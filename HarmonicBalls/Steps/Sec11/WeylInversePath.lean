import HarmonicBalls.Steps.Sec11.WeylLengthDerivative

/-! # Inverse Weyl cost of a reparametrized path

The original length of a unit-speed curve is the inverse Weyl cost of its
shifted-length parametrization. -/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- Reparametrizing an original unit-speed curve by shifted length gives an
inverse-Weyl path whose cost is the original length. -/
theorem IsEuclideanLengthMetric.exists_inverse_weyl_path
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ c : ℝ} (hξ : 0 ≤ ξ) (f : ℂ → ℝ) (hf : Continuous f)
    (hl : ∀ z, c ≤ f z) (hu : ∀ z, f z ≤ 0)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T)
    (hE : IsEuclideanLengthMetric (fun u v => (weylScaling D ξ f u v).toReal)) :
    ∃ S q, IsLengthParametrized (fun u v => (weylScaling D ξ f u v).toReal) q S ∧
      q 0 = p 0 ∧ q S = p T ∧
      (∫⁻ s in Icc 0 S, ENNReal.ofReal (Real.exp (ξ * (-f (q s))))) = ENNReal.ofReal T ∧
      S = (curveLength (fun u v => (weylScaling D ξ f u v).toReal) p 0 T).toReal ∧
      ∀ t ∈ Icc 0 T, q (curveLength (fun u v => (weylScaling D ξ f u v).toReal) p 0 t).toReal = p t := by
  let E : ℂ → ℂ → ℝ := fun u v => (weylScaling D ξ f u v).toReal
  let L : ℝ → ℝ := fun t => (curveLength E p 0 t).toReal
  have hED : ∀ u v, E u v ≤ D u v := fun u v =>
    (weylScaling_negative_bump_real_bounds hD hξ f hl hu (hD.weylScaling_zero ξ) u v).2.2
  have hfin : curveLength E p 0 T < ∞ :=
    lt_of_le_of_lt (curveLength_le_of_lengthParametrized_of_le hp hED le_rfl hp.1 le_rfl)
      ENNReal.ofReal_lt_top
  obtain ⟨q, hq, hq0, hqT, htrack⟩ := hE.exists_lengthParametrized_with_tracking hp.1 hp.2.1 hfin
  refine ⟨L T, q, hq, hq0, hqT, ?_, rfl, htrack⟩
  have hLzero : L 0 = 0 := by
    have h := curveLength_le_of_lengthParametrized_of_le hp hED le_rfl le_rfl hp.1
    have hz : curveLength E p 0 0 = 0 := by simpa using (nonpos_iff_eq_zero.mp (by simpa using h))
    simp [L, hz]
  have hLcont : ContinuousOn L (Icc 0 T) := (hE.cumulative_curveLength_lipschitzOn hp hED).continuousOn
  have hLrange : L '' Icc 0 T ⊆ Icc 0 (L T) := by
    rintro u ⟨t, ht, rfl⟩
    constructor
    · exact ENNReal.toReal_nonneg
    · have h := (hE.cumulative_curveLength_increment_bounds hp hED ht.1 ht.2 le_rfl).1
      dsimp [L] at *
      linarith
  let w : ℝ → ℝ := fun t => Real.exp (ξ * f (p t))
  let g : ℝ → ℝ := fun s => Real.exp (ξ * (-f (q s)))
  have hwcont : ContinuousOn w (Icc 0 T) :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul (hf.comp_continuousOn hp.2.1))
  have hgcont : ContinuousOn g (Icc 0 (L T)) :=
    Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul ((hf.comp_continuousOn hq.2.1).neg))
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivWithinAt L (w t) (Ioi t) t := by
    intro t ht
    exact (hD.hasDerivAt_weylScaling_curveLength hξ f hf hl hu hp ht hE).hasDerivWithinAt
  have hsubst := intervalIntegral.integral_comp_mul_deriv''
    (a := 0) (b := T) (f := L) (f' := w) (g := g)
    (by simpa only [uIcc_of_le hp.1] using hLcont)
    (by simpa only [min_eq_left hp.1, max_eq_right hp.1] using hderiv)
    (by simpa only [uIcc_of_le hp.1] using hwcont)
    (by simpa only [uIcc_of_le hp.1] using hgcont.mono hLrange)
  have hprod : ∀ t ∈ Icc 0 T, (g ∘ L) t * w t = 1 := by
    intro t ht
    dsimp only [Function.comp_apply, g, w, L]
    rw [htrack t ht, ← Real.exp_add]
    have heq : ξ * -f (p t) + ξ * f (p t) = 0 := by ring
    rw [heq, Real.exp_zero]
  have hint : (∫ t in (0 : ℝ)..T, (g ∘ L) t * w t) = T := by
    calc
      _ = ∫ _t in (0 : ℝ)..T, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hp.1]
        intro t ht
        exact hprod t ht
      _ = T := by simp
  rw [hint, hLzero] at hsubst
  have hS : 0 ≤ L T := ENNReal.toReal_nonneg
  have hconv := ofReal_integral_eq_lintegral_ofReal
    (hgcont.integrableOn_Icc (μ := volume)) (Filter.Eventually.of_forall fun s => Real.exp_nonneg _)
  have hinterval : (∫ s in (0 : ℝ)..L T, g s) = ∫ s in Icc 0 (L T), g s := by
    rw [intervalIntegral.integral_of_le hS, Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume))]
  rw [← hconv, ← hinterval, ← hsubst]

/-- The inverse Weyl distance is at most the original distance. -/
theorem IsEuclideanLengthMetric.inverse_weylScaling_le
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ c : ℝ} (hξ : 0 ≤ ξ) (f : ℂ → ℝ) (hf : Continuous f)
    (hl : ∀ z, c ≤ f z) (hu : ∀ z, f z ≤ 0)
    (hE : IsEuclideanLengthMetric (fun u v => (weylScaling D ξ f u v).toReal))
    (x y : ℂ) :
    weylScaling (fun u v => (weylScaling D ξ f u v).toReal) ξ (fun z => -f z) x y ≤
      ENNReal.ofReal (D x y) := by
  rw [← hD.weylScaling_zero ξ x y]
  unfold weylScaling at ⊢
  refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun hp0 =>
    le_iInf fun hpT => ?_
  obtain ⟨S, q, hq, hq0, hqS, hcost, _, _⟩ := hD.exists_inverse_weyl_path hξ f hf hl hu hp hE
  have hq0' : q 0 = x := hq0.trans hp0
  have hqS' : q S = y := hqS.trans hpT
  have h : weylScaling (fun u v => (weylScaling D ξ f u v).toReal) ξ (fun z => -f z) x y ≤
      ∫⁻ s in Icc 0 S, ENNReal.ofReal (Real.exp (ξ * (-f (q s)))) := by
    unfold weylScaling
    exact (iInf₂_le S q).trans ((iInf₂_le hq hq0').trans (iInf_le _ hqS'))
  change weylScaling (fun u v => (weylScaling D ξ f u v).toReal) ξ (fun z => -f z) x y ≤
    ∫⁻ t in Icc (0 : ℝ) T, ENNReal.ofReal (Real.exp (ξ * (0 : ℂ → ℝ) (p t)))
  simpa only [Pi.zero_apply, mul_zero, Real.exp_zero, ENNReal.ofReal_one,
    lintegral_const, one_mul, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, hcost] using h

#print axioms IsEuclideanLengthMetric.inverse_weylScaling_le
#print axioms IsEuclideanLengthMetric.exists_inverse_weyl_path

end HarmonicBalls
