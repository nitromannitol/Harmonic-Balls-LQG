import HarmonicBalls.Proofs.Sec6.BrownianScaling
import HarmonicBalls.Proofs.Brownian.PlanarHeatSemigroup
import HarmonicBalls.Defs.Brownian
import LatticeProb.Prob.GaussianFreezing
import LatticeProb.Analysis.ExpDampedRieszKernelQuadrant

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

/-- The subcritical Riesz kernel has finite Lebesgue energy on the unit square. -/
theorem lintegral_unit_square_abs_sub_rpow_lt_top {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (|p.1 - p.2| ^ (-q))
      ∂((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1)))) < ∞ := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let ν : Measure ℝ := volume.restrict (Ici (0 : ℝ))
  have hμν : μ ≤ ν := Measure.restrict_mono_set volume (by intro x hx; exact hx.1)
  have hdamp : (∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal (Real.exp (-max p.1 p.2) * |p.1 - p.2| ^ (-q)) ∂(ν.prod ν)) < ∞ := by
    simpa [ν, show (1 - q) - 1 = -q by ring] using
      (LatticeProb.Analysis.lintegral_exp_neg_max_mul_abs_sub_rpow_lt_top
        (c := 1) (θ := 1 - q) (by norm_num) (by linarith) (by linarith))
  have hmem : ∀ᵐ p ∂(μ.prod μ), p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  have hbound : ∀ᵐ p ∂(μ.prod μ),
      ENNReal.ofReal (|p.1 - p.2| ^ (-q)) ≤
        ENNReal.ofReal (Real.exp 1) *
          ENNReal.ofReal (Real.exp (-max p.1 p.2) * |p.1 - p.2| ^ (-q)) := by
    filter_upwards [hmem] with p hp
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have hexp : 1 ≤ Real.exp 1 * Real.exp (-max p.1 p.2) := by
      rw [← Real.exp_add]
      have h : 0 ≤ (1 : ℝ) + -max p.1 p.2 := by
        linarith [max_le hp.1.2 hp.2.2]
      simpa using Real.exp_le_exp.mpr h
    nlinarith [Real.rpow_nonneg (abs_nonneg (p.1 - p.2)) (-q)]
  calc
    _ ≤ ∫⁻ p, ENNReal.ofReal (Real.exp 1) *
        ENNReal.ofReal (Real.exp (-max p.1 p.2) * |p.1 - p.2| ^ (-q)) ∂(μ.prod μ) :=
      lintegral_mono_ae hbound
    _ ≤ ∫⁻ p, ENNReal.ofReal (Real.exp 1) *
        ENNReal.ofReal (Real.exp (-max p.1 p.2) * |p.1 - p.2| ^ (-q)) ∂(ν.prod ν) :=
      lintegral_mono' (Measure.prod_mono hμν hμν) le_rfl
    _ = ENNReal.ofReal (Real.exp 1) * ∫⁻ p,
        ENNReal.ofReal (Real.exp (-max p.1 p.2) * |p.1 - p.2| ^ (-q)) ∂(ν.prod ν) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hdamp

/-- The unit-time occupation measure has finite subcritical time energy. -/
theorem lintegral_unit_time_abs_sub_rpow_lt_top {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    (∫⁻ p : ℝ≥0 × ℝ≥0, ENNReal.ofReal (|(p.1 : ℝ) - (p.2 : ℝ)| ^ (-q))
      ∂(ν.prod ν)) < ∞ := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hm : Measurable Real.toNNReal := continuous_real_toNNReal.measurable
  have hf : Measurable (fun p : ℝ≥0 × ℝ≥0 =>
      ENNReal.ofReal (|(p.1 : ℝ) - (p.2 : ℝ)| ^ (-q))) := by
    fun_prop
  change (∫⁻ p : ℝ≥0 × ℝ≥0, ENNReal.ofReal (|(p.1 : ℝ) - (p.2 : ℝ)| ^ (-q))
    ∂((Measure.map Real.toNNReal μ).prod (Measure.map Real.toNNReal μ))) < ∞
  rw [Measure.map_prod_map _ _ hm hm, lintegral_map hf (hm.prodMap hm)]
  have hmem : ∀ᵐ p ∂(μ.prod μ), p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  have heq : (∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal (|((Real.toNNReal p.1 : ℝ≥0) : ℝ) -
        ((Real.toNNReal p.2 : ℝ≥0) : ℝ)| ^ (-q)) ∂(μ.prod μ)) =
      ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (|p.1 - p.2| ^ (-q)) ∂(μ.prod μ) := by
    apply lintegral_congr_ae
    filter_upwards [hmem] with p hp
    simp [Real.toNNReal_of_nonneg hp.1.1, Real.toNNReal_of_nonneg hp.2.1]
  change (∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal (|((Real.toNNReal p.1 : ℝ≥0) : ℝ) -
        ((Real.toNNReal p.2 : ℝ≥0) : ℝ)| ^ (-q)) ∂(μ.prod μ)) < ∞
  rw [heq]
  exact lintegral_unit_square_abs_sub_rpow_lt_top hq0 hq1

/-- A subcritical power bound for the small-ball probability of a Brownian increment. -/
theorem planarBrownianMotion_increment_smallBall_rpow_le (x : ℂ)
    {s t : ℝ≥0} (hts : t ≠ s) {r q : ℝ} (hr : 0 < r) (hq0 : 0 < q) (hq1 : q < 1) :
    planarBrownianMotion x {b | ‖b t - b s‖ < r} ≤
      ENNReal.ofReal ((2 / Real.pi) ^ q * r ^ (2 * q) *
        |(t : ℝ) - (s : ℝ)| ^ (-q)) := by
  let u : ℝ := |(t : ℝ) - (s : ℝ)|
  have hu : 0 < u := by
    dsimp [u]
    apply abs_pos.mpr
    exact sub_ne_zero.mpr (by exact_mod_cast hts)
  let a : ℝ := 2 * r / Real.sqrt (2 * Real.pi * u)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hs : (Real.sqrt (2 * Real.pi * u)) ^ 2 = 2 * Real.pi * u :=
    Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (2 * Real.pi * u) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hu0 : u ≠ 0 := ne_of_gt hu
  have haeq : a ^ 2 = (2 / Real.pi) * r ^ 2 / u := by
    dsimp [a]
    field_simp
    nlinarith [hs]
  have hpower : (a ^ 2) ^ q =
      (2 / Real.pi) ^ q * r ^ (2 * q) * u ^ (-q) := by
    rw [haeq, Real.div_rpow (by positivity) (le_of_lt hu),
      Real.mul_rpow (by positivity) (sq_nonneg r),
      ← Real.rpow_natCast r 2, ← Real.rpow_mul (le_of_lt hr),
      Real.rpow_neg (le_of_lt hu)]
    ring
  have hmin : min 1 (ENNReal.ofReal (a ^ 2)) ≤ ENNReal.ofReal ((a ^ 2) ^ q) := by
    by_cases h : a ^ 2 ≤ 1
    · exact (min_le_right _ _).trans
        (ENNReal.ofReal_le_ofReal (Real.self_le_rpow_of_le_one (sq_nonneg a) h hq1.le))
    · have hh : 1 ≤ (a ^ 2) ^ q := Real.one_le_rpow (le_of_not_ge h) hq0.le
      exact (min_le_left _ _).trans (by simpa using ENNReal.ofReal_le_ofReal hh)
  have hsmall := planarBrownianMotion_increment_smallBall_le x hts hr.le
  have hsmall' : planarBrownianMotion x {b | ‖b t - b s‖ < r} ≤
      min 1 (ENNReal.ofReal (a ^ 2)) := by
    simpa only [a, u, coe_nndist, Real.dist_eq, ENNReal.ofReal_pow ha] using hsmall
  exact hsmall'.trans (by simpa [hpower, u] using hmin)

/-- Expected unit-time pair occupation of planar Brownian motion obeys every power
bound of exponent strictly between zero and two. -/
theorem planarBrownianMotion_unit_pair_occupation_le (x : ℂ) {d : ℝ}
    (hd0 : 0 < d) (hd2 : d < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      (∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0,
        (if ‖b p.1 - b p.2‖ < r then 1 else 0 : ℝ≥0∞) ∂(ν.prod ν)
          ∂(planarBrownianMotion x)) ≤ ENNReal.ofReal (C * r ^ d) := by
  let q : ℝ := d / 2
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hqd : 2 * q = d := by dsimp [q]; ring
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let K : ℝ≥0∞ := ∫⁻ p : ℝ≥0 × ℝ≥0,
    ENNReal.ofReal (|(p.1 : ℝ) - (p.2 : ℝ)| ^ (-q)) ∂(ν.prod ν)
  have hK : K < ∞ := lintegral_unit_time_abs_sub_rpow_lt_top hq0 hq1
  let C : ℝ := (2 / Real.pi) ^ q * (K.toReal + 1)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro r hr
  have hν : NullSingletonClass ν := by
    constructor
    intro t
    dsimp [ν]
    rw [Measure.map_apply continuous_real_toNNReal.measurable (measurableSet_singleton t),
      Measure.restrict_apply (continuous_real_toNNReal.measurable (measurableSet_singleton t))]
    apply measure_mono_null _ (measure_singleton (t : ℝ))
    intro z hz
    have ht := congrArg (fun v : ℝ≥0 => (v : ℝ)) hz.1
    have hz0 : 0 ≤ z := hz.2.1
    simpa [Real.toNNReal_of_nonneg hz0] using ht
  let : NullSingletonClass ν := hν
  have hd : (ν.prod ν) (Set.diagonal ℝ≥0) = 0 := by
    apply Measure.measure_prod_null_of_ae_null measurableSet_diagonal
    filter_upwards [] with t
    simp [Set.diagonal]
  have hae : ∀ᵐ p ∂(ν.prod ν), p.1 ≠ p.2 := by
    have h := measure_eq_zero_iff_ae_notMem.1 hd
    simpa [Set.diagonal] using h
  have hA : 0 ≤ (2 / Real.pi) ^ q * r ^ d := by positivity
  have hKbound : K ≤ ENNReal.ofReal (K.toReal + 1) := by
    calc
      K = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hK.ne).symm
      _ ≤ ENNReal.ofReal (K.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  calc
    _ = ∫⁻ p : ℝ≥0 × ℝ≥0,
        planarBrownianMotion x {b | ‖b p.1 - b p.2‖ < r} ∂(ν.prod ν) :=
      lintegral_pair_occupation_eq x r ν
    _ ≤ ∫⁻ p : ℝ≥0 × ℝ≥0, ENNReal.ofReal ((2 / Real.pi) ^ q * r ^ d *
        |(p.1 : ℝ) - (p.2 : ℝ)| ^ (-q)) ∂(ν.prod ν) := by
      apply lintegral_mono_ae
      filter_upwards [hae] with p hp
      simpa [hqd] using planarBrownianMotion_increment_smallBall_rpow_le x hp hr hq0 hq1
    _ = ENNReal.ofReal ((2 / Real.pi) ^ q * r ^ d) * K := by
      simp_rw [ENNReal.ofReal_mul hA]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal ((2 / Real.pi) ^ q * r ^ d) *
        ENNReal.ofReal (K.toReal + 1) := by gcongr
    _ = ENNReal.ofReal (C * r ^ d) := by
      rw [← ENNReal.ofReal_mul hA]
      congr 1
      dsimp [C]
      ring

end HarmonicBalls
