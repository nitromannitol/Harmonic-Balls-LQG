import HarmonicBalls.Proofs.Brownian.PlanarBrownianMotion
import HarmonicBalls.Proofs.Brownian.PlanarHeatFeller

/-! # Occupation density of planar Brownian motion from the origin

The law of planar Brownian motion from the origin at a positive time `s` has the Gaussian
density `(2 π s)⁻¹ exp (-|z|² / (2 s))`. Integrating over `s ∈ (0, T]` and using
`exp (-u) ≤ u ^ (-θ)` for `θ ∈ (0, 1]`, the expected occupation of a nonnegative density up
to time `T` is at most a constant times its integral against `|z| ^ (-2 θ)`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The marginal of planar Brownian motion at a fixed time is the planar Gaussian. -/
theorem planarBrownianMotion_map_eval_eq (x : ℂ) (t : ℝ≥0) :
    (planarBrownianMotion x).map (fun b => b t) = planarGaussian x t := by
  have hmap := isFellerKernelSemigroup_planarHeatSemigroup.continuousProcess_map_eval_nnreal
    planarHeatSemigroup isConservative_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup t
  rw [← planarBrownianMotion_eq_continuousProcess] at hmap
  have hvalue := congrArg (fun ker : ProbabilityTheory.Kernel ℂ ℂ => ker x) hmap
  change (planarBrownianMotion.map (ContinuousPath.coordinateProcess t)) x = _ at hvalue
  rw [ProbabilityTheory.Kernel.map_apply _ (ContinuousPath.measurable_coordinateProcess t),
    planarHeatSemigroup_apply] at hvalue
  exact hvalue

/-- The centred planar Gaussian of positive variance has the radial Gaussian density. -/
theorem lintegral_planarGaussian_zero_eq {t : ℝ≥0} (ht : t ≠ 0) (f : ℂ → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ z, f z ∂planarGaussian 0 t =
      ∫⁻ z, f z * ENNReal.ofReal ((2 * Real.pi * t)⁻¹ * Real.exp (-‖z‖ ^ 2 / (2 * t))) := by
  have he := Complex.measurableEquivRealProd.symm.measurable
  have hg : Measurable (fun p : ℝ × ℝ => gaussianPDF 0 t p.1 * gaussianPDF 0 t p.2) :=
    ((measurable_gaussianPDF 0 t).comp measurable_fst).mul
      ((measurable_gaussianPDF 0 t).comp measurable_snd)
  have hG : Measurable (fun p : ℝ × ℝ => (gaussianPDF 0 t p.1 * gaussianPDF 0 t p.2) *
      f (Complex.measurableEquivRealProd.symm p)) := hg.mul (hf.comp he)
  calc ∫⁻ z, f z ∂planarGaussian 0 t
      = ∫⁻ p, f (Complex.measurableEquivRealProd.symm p)
          ∂((gaussianReal 0 t).prod (gaussianReal 0 t)) := by
        rw [planarGaussian, Complex.zero_re, Complex.zero_im, lintegral_map hf he]
    _ = ∫⁻ p, f (Complex.measurableEquivRealProd.symm p)
          ∂((volume.prod volume).withDensity
            (fun p : ℝ × ℝ => gaussianPDF 0 t p.1 * gaussianPDF 0 t p.2)) := by
        rw [gaussianReal_of_var_ne_zero 0 ht,
          prod_withDensity (measurable_gaussianPDF 0 t) (measurable_gaussianPDF 0 t)]
    _ = ∫⁻ p, (gaussianPDF 0 t p.1 * gaussianPDF 0 t p.2) *
          f (Complex.measurableEquivRealProd.symm p) ∂(volume.prod volume) :=
        lintegral_withDensity_eq_lintegral_mul _ hg (hf.comp he)
    _ = ∫⁻ p, (gaussianPDF 0 t p.1 * gaussianPDF 0 t p.2) *
          f (Complex.measurableEquivRealProd.symm p) := by rw [Measure.volume_eq_prod]
    _ = ∫⁻ z, (gaussianPDF 0 t (Complex.measurableEquivRealProd z).1 *
          gaussianPDF 0 t (Complex.measurableEquivRealProd z).2) *
          f (Complex.measurableEquivRealProd.symm (Complex.measurableEquivRealProd z)) :=
        (Complex.volume_preserving_equiv_real_prod.lintegral_comp hG).symm
    _ = _ := by
        apply lintegral_congr
        intro z
        have h1 : (Complex.measurableEquivRealProd z).1 = z.re := rfl
        have h2 : (Complex.measurableEquivRealProd z).2 = z.im := rfl
        have h3 : Complex.measurableEquivRealProd.symm (Complex.measurableEquivRealProd z) = z :=
          Complex.measurableEquivRealProd.symm_apply_apply z
        simp only [h1, h2, h3]
        rw [mul_comm (f z)]
        congr 1
        have ht' : (0 : ℝ) < t := by
          have := t.coe_nonneg
          exact lt_of_le_of_ne this (by exact_mod_cast (Ne.symm ht))
        have hs : 0 < Real.sqrt (2 * Real.pi * t) := Real.sqrt_pos.mpr (by positivity)
        simp only [gaussianPDF_def, gaussianPDFReal]
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have hsq : Real.sqrt (2 * Real.pi * t) ^ 2 = 2 * Real.pi * t := Real.sq_sqrt (by positivity)
        have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          ring
        rw [hn, show -(z.re ^ 2 + z.im ^ 2) / (2 * (t : ℝ)) =
            -(z.re - 0) ^ 2 / (2 * t) + -(z.im - 0) ^ 2 / (2 * t) by ring, Real.exp_add]
        field_simp
        rw [hsq]

/-- For `u > 0` and `θ ∈ [0, 1]`, `exp (-u) ≤ u ^ (-θ)`. -/
theorem exp_neg_le_rpow_neg {u θ : ℝ} (hu : 0 < u) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.exp (-u) ≤ u ^ (-θ) := by
  have hle : u ^ θ ≤ Real.exp u := by
    by_cases h1 : u ≤ 1
    · exact (Real.rpow_le_one hu.le h1 hθ0).trans (Real.one_le_exp hu.le)
    · have h1' : 1 ≤ u := le_of_lt (not_le.mp h1)
      calc u ^ θ ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1' hθ1
        _ = u := Real.rpow_one u
        _ ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  rw [Real.exp_neg, Real.rpow_neg hu.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hu θ) hle

/-- The Gaussian density at time `s` is at most `(2 π)⁻¹ 2^θ s^(θ-1) |z|^(-2θ)`. -/
theorem ofReal_heatDensity_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {s : ℝ} (hs : 0 < s)
    (z : ℂ) :
    ENNReal.ofReal ((2 * Real.pi * s)⁻¹ * Real.exp (-‖z‖ ^ 2 / (2 * s))) ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * s ^ (θ - 1)) *
        ENNReal.ofReal ‖z‖ ^ (-(2 * θ)) := by
  by_cases hz : z = 0
  · subst hz
    rw [norm_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by linarith),
      ENNReal.mul_top (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)]
    exact le_top
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hu : 0 < ‖z‖ ^ 2 / (2 * s) := by positivity
    rw [ENNReal.ofReal_rpow_of_pos hn, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have he := exp_neg_le_rpow_neg hu hθ0.le hθ1
    rw [show -‖z‖ ^ 2 / (2 * s) = -(‖z‖ ^ 2 / (2 * s)) by ring]
    have hrw : (‖z‖ ^ 2 / (2 * s)) ^ (-θ) = 2 ^ θ * s ^ θ * ‖z‖ ^ (-(2 * θ)) := by
      rw [Real.rpow_neg (by positivity), Real.div_rpow (by positivity) (by positivity), inv_div,
        Real.mul_rpow (by norm_num) hs.le, ← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul hn.le,
        div_eq_mul_inv, ← Real.rpow_neg hn.le]
      norm_num
    calc (2 * Real.pi * s)⁻¹ * Real.exp (-(‖z‖ ^ 2 / (2 * s)))
        ≤ (2 * Real.pi * s)⁻¹ * (‖z‖ ^ 2 / (2 * s)) ^ (-θ) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = (2 * Real.pi)⁻¹ * 2 ^ θ * s ^ (θ - 1) * ‖z‖ ^ (-(2 * θ)) := by
          rw [hrw, Real.rpow_sub hs, Real.rpow_one]
          field_simp

/-- **Occupation from the origin.** The expected occupation of a nonnegative density by
planar Brownian motion from the origin during `(0, T]` is at most
`(2 π)⁻¹ 2^θ T^θ / θ` times the integral of the density against `|z| ^ (-2 θ)`. -/
theorem lintegral_planarBrownianMotion_zero_occupation_le {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) {T : ℝ} (hT : 0 ≤ T) (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ b, (∫⁻ s in Ioc 0 T, f (b s.toNNReal)) ∂planarBrownianMotion 0) ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * (T ^ θ / θ)) *
        ∫⁻ z, f z * ENNReal.ofReal ‖z‖ ^ (-(2 * θ)) := by
  have hev : Measurable (fun p : ContinuousPath ℂ × ℝ => p.1 p.2.toNNReal) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  set K := ∫⁻ z, f z * ENNReal.ofReal ‖z‖ ^ (-(2 * θ)) with hK
  rw [lintegral_lintegral_swap (f := fun (b : ContinuousPath ℂ) (s : ℝ) => f (b s.toNNReal))
    (hf.comp hev).aemeasurable]
  have hpt : ∀ s ∈ Ioc (0 : ℝ) T, (∫⁻ b, f (b s.toNNReal) ∂planarBrownianMotion 0) ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * s ^ (θ - 1)) * K := by
    intro s hs
    have hs0 : s.toNNReal ≠ 0 := (Real.toNNReal_pos.mpr hs.1).ne'
    have hev1 : Measurable (fun b : ContinuousPath ℂ => b s.toNNReal) :=
      ContinuousPath.measurable_coordinateProcess _
    rw [← lintegral_map hf hev1, planarBrownianMotion_map_eval_eq,
      lintegral_planarGaussian_zero_eq hs0 f hf, hK, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro z
    dsimp only
    rw [mul_left_comm]
    gcongr
    have h := ofReal_heatDensity_le hθ0 hθ1 hs.1 z
    rwa [Real.coe_toNNReal _ hs.1.le]
  calc (∫⁻ s in Ioc 0 T, ∫⁻ b, f (b s.toNNReal) ∂planarBrownianMotion 0)
      ≤ ∫⁻ s in Ioc 0 T, ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * s ^ (θ - 1)) * K :=
        setLIntegral_mono' measurableSet_Ioc hpt
    _ = (∫⁻ s in Ioc 0 T, ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * s ^ (θ - 1))) * K := by
        exact lintegral_mul_const _
          (ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_id.pow_const _)))
    _ = _ := by
        congr 1
        have hint : IntervalIntegrable (fun s : ℝ => (2 * Real.pi)⁻¹ * 2 ^ θ * s ^ (θ - 1))
            volume 0 T :=
          (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _
        rw [← ofReal_integral_eq_lintegral_ofReal
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hint)
          ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs => by
            have := hs.1
            positivity)), ← intervalIntegral.integral_of_le hT,
          intervalIntegral.integral_const_mul,
          integral_rpow (Or.inl (by linarith : (-1 : ℝ) < θ - 1))]
        congr 1
        rw [show θ - 1 + 1 = θ by ring, Real.zero_rpow hθ0.ne', sub_zero]

end HarmonicBalls
