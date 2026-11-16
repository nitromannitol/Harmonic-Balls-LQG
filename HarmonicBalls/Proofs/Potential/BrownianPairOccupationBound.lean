import HarmonicBalls.Proofs.Sec6.BrownianScaling
import HarmonicBalls.Proofs.Brownian.PlanarHeatSemigroup
import HarmonicBalls.Defs.Brownian
import LatticeProb.Prob.GaussianFreezing

/-! # Planar Brownian increments

Planar Brownian increments have centered Gaussian laws and satisfy a small-ball bound.
A Tonelli identity expresses expected pair occupation in terms of increment probabilities.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- Each planar Brownian increment has the centered Gaussian law with variance equal to
the time difference. -/
theorem planarBrownianMotion_map_increment (x : ℂ) (s t : ℝ≥0) :
    (planarBrownianMotion x).map (fun b => b t - b s) =
      planarGaussian 0 (nndist (t : ℝ) (s : ℝ)) := by
  let f : ContinuousPath ℝ → ℝ := fun b => b t - b s
  have hf : Measurable f := (ContinuousPath.measurable_coordinateProcess _).sub
    (ContinuousPath.measurable_coordinateProcess _)
  have hlaw (a : ℝ) : (brownianMotion a).map f = gaussianReal 0 (nndist (t : ℝ) (s : ℝ)) := by
    have h := (HarmonicBalls.Section6.isPreBrownianReal_brownianMotion a).hasLaw_sub t s
    change HasLaw (fun b : ContinuousPath ℝ => (b t - a) - (b s - a)) _ _ at h
    simpa [f, sub_sub_sub_cancel_right] using h.map_eq
  have hF : Measurable (fun b : ContinuousPath ℂ => b t - b s) :=
    (ContinuousPath.measurable_coordinateProcess _).sub (ContinuousPath.measurable_coordinateProcess _)
  have hp : ((brownianMotion x.re).prod (brownianMotion x.im)).map (Prod.map f f) =
      (gaussianReal 0 (nndist (t : ℝ) (s : ℝ))).prod
        (gaussianReal 0 (nndist (t : ℝ) (s : ℝ))) := by
    rw [← Measure.map_prod_map _ _ hf hf, hlaw x.re, hlaw x.im]
  have hff : Measurable (Prod.map f f) := (hf.comp measurable_fst).prodMk (hf.comp measurable_snd)
  rw [planarBrownianMotion_apply, Measure.map_map hF measurable_complexPathOfReIm,
    planarGaussian, Complex.zero_re, Complex.zero_im, ← hp,
    Measure.map_map Complex.measurableEquivRealProd.symm.measurable hff]
  congr 1
  funext p
  simp only [Function.comp_apply, complexPathOfReIm_apply, f]
  apply Complex.ext <;> simp [Complex.measurableEquivRealProd]

/-- A planar Gaussian assigns a ball at most the product of the coordinate interval bounds. -/
theorem planarGaussian_ball_le {v : ℝ≥0} (hv : v ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    planarGaussian 0 v (ball 0 r) ≤
      (ENNReal.ofReal (2 * r / Real.sqrt (2 * Real.pi * v))) ^ 2 := by
  let I : Set ℝ := Icc (-r) r
  have hsub : Complex.measurableEquivRealProd.symm ⁻¹' (ball (0 : ℂ) r) ⊆ I ×ˢ I := by
    intro p hp
    have hn : ‖Complex.measurableEquivRealProd.symm p‖ < r := by
      simpa [Metric.mem_ball, dist_zero_right] using hp
    have hre : |p.1| ≤ r := (Complex.abs_re_le_norm _).trans (le_of_lt hn)
    have him : |p.2| ≤ r := (Complex.abs_im_le_norm _).trans (le_of_lt hn)
    exact ⟨abs_le.mp hre, abs_le.mp him⟩
  have hI : gaussianReal 0 v I ≤ ENNReal.ofReal (2 * r / Real.sqrt (2 * Real.pi * v)) := by
    have h := LatticeProb.gaussianReal_Icc_le hv (c := -r) (d := r) (by linarith)
    simpa [I, show r - -r = 2 * r by ring] using h
  rw [planarGaussian, Complex.zero_re, Complex.zero_im,
    Measure.map_apply Complex.measurableEquivRealProd.symm.measurable isOpen_ball.measurableSet]
  calc
    _ ≤ ((gaussianReal 0 v).prod (gaussianReal 0 v)) (I ×ˢ I) := measure_mono hsub
    _ = gaussianReal 0 v I * gaussianReal 0 v I := Measure.prod_prod _ _
    _ ≤ (ENNReal.ofReal (2 * r / Real.sqrt (2 * Real.pi * v))) ^ 2 := by
      simpa [pow_two] using mul_le_mul' hI hI

/-- A planar Brownian increment satisfies a two-dimensional small-ball bound. -/
theorem planarBrownianMotion_increment_smallBall_le (x : ℂ) {s t : ℝ≥0} (hts : t ≠ s) {r : ℝ} (hr : 0 ≤ r) :
    planarBrownianMotion x {b | ‖b t - b s‖ < r} ≤
      min 1 ((ENNReal.ofReal (2 * r / Real.sqrt (2 * Real.pi *
        (nndist (t : ℝ) (s : ℝ) : ℝ)))) ^ 2) := by
  have hv : nndist (t : ℝ) (s : ℝ) ≠ 0 := by
    intro hzero
    apply hts
    exact_mod_cast (nndist_eq_zero.mp hzero)
  apply le_min
  · exact prob_le_one
  · have hm : Measurable (fun b : MarkovProcess.ContinuousPath ℂ => b t - b s) :=
      (MarkovProcess.ContinuousPath.measurable_coordinateProcess _).sub
        (MarkovProcess.ContinuousPath.measurable_coordinateProcess _)
    have h := congrArg (fun μ : Measure ℂ => μ (ball 0 r))
      (planarBrownianMotion_map_increment x s t)
    rw [Measure.map_apply hm isOpen_ball.measurableSet] at h
    have hh : planarBrownianMotion x {b | ‖b t - b s‖ < r} =
        planarGaussian 0 (nndist (t : ℝ) (s : ℝ)) (ball 0 r) := by
      change planarBrownianMotion x {b | dist (b t - b s) 0 < r} = _ at h
      simpa only [dist_zero_right] using h
    rw [hh]
    exact planarGaussian_ball_le hv hr

/-- Expected pair occupation is the integral of the two-time small-ball probabilities. -/
theorem lintegral_pair_occupation_eq (x : ℂ) (r : ℝ) (ν : Measure ℝ≥0) [SFinite ν] :
    (∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0,
      (if ‖b p.1 - b p.2‖ < r then 1 else 0 : ℝ≥0∞) ∂(ν.prod ν)
        ∂(planarBrownianMotion x)) =
    ∫⁻ p : ℝ≥0 × ℝ≥0,
      planarBrownianMotion x {b | ‖b p.1 - b p.2‖ < r} ∂(ν.prod ν) := by
  let E : Set (ContinuousPath ℂ × (ℝ≥0 × ℝ≥0)) :=
    {p | ‖p.1 p.2.1 - p.1 p.2.2‖ < r}
  have hE : MeasurableSet E := by
    apply isOpen_lt _ continuous_const |>.measurableSet
    fun_prop
  let F : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0) → ℝ≥0∞ := E.indicator 1
  have hF : Measurable F := measurable_const.indicator hE
  calc
    _ = ∫⁻ b, ∫⁻ p, F (b,p) ∂(ν.prod ν) ∂(planarBrownianMotion x) := by
      simp [F, E, Set.indicator_apply]
    _ = ∫⁻ p, ∫⁻ b, F (b,p) ∂(planarBrownianMotion x) ∂(ν.prod ν) :=
      lintegral_lintegral_swap hF.aemeasurable
    _ = _ := by
      congr 1; funext p
      have hm : MeasurableSet {b : ContinuousPath ℂ | ‖b p.1 - b p.2‖ < r} := by
        apply isOpen_lt _ continuous_const |>.measurableSet
        fun_prop
      convert lintegral_indicator_one hm using 1; simp [F, E, Set.indicator_apply]

/-- For an atomless time measure, the expected pair occupation is bounded by the
integral of the two-dimensional Gaussian small-ball bound. -/
theorem lintegral_pair_occupation_le (x : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (ν : Measure ℝ≥0) [SFinite ν] [NullSingletonClass ν] :
    (∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0,
      (if ‖b p.1 - b p.2‖ < r then 1 else 0 : ℝ≥0∞) ∂(ν.prod ν)
        ∂(planarBrownianMotion x)) ≤
    ∫⁻ p : ℝ≥0 × ℝ≥0, min 1
      ((ENNReal.ofReal (2 * r / Real.sqrt (2 * Real.pi *
        (nndist (p.1 : ℝ) (p.2 : ℝ) : ℝ)))) ^ 2) ∂(ν.prod ν) := by
  rw [lintegral_pair_occupation_eq]
  have hd : (ν.prod ν) (Set.diagonal ℝ≥0) = 0 := by
    apply Measure.measure_prod_null_of_ae_null measurableSet_diagonal
    filter_upwards [] with t
    simp [Set.diagonal]
  have hae : ∀ᵐ p ∂(ν.prod ν), p.1 ≠ p.2 := by
    have h := measure_eq_zero_iff_ae_notMem.1 hd
    simpa [Set.diagonal] using h
  apply lintegral_mono_ae
  filter_upwards [hae] with p hp
  exact planarBrownianMotion_increment_smallBall_le x hp hr

end HarmonicBalls
