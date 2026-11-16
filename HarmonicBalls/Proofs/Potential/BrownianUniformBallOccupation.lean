import HarmonicBalls.Proofs.Potential.BrownianPairOccupationBound

/-! # Uniform-centre Brownian increment estimates

Planar Brownian increments satisfy a small-ball bound uniform in the centre.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- A centred planar Gaussian assigns every ball at most the product of the
coordinate interval bounds. -/
theorem planarGaussian_ball_le_uniform_center {v : ℝ≥0} (hv : v ≠ 0)
    (z : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    planarGaussian 0 v (ball z r) ≤
      (ENNReal.ofReal (2 * r / Real.sqrt (2 * Real.pi * v))) ^ 2 := by
  let I : Set ℝ := Icc (z.re - r) (z.re + r)
  let J : Set ℝ := Icc (z.im - r) (z.im + r)
  have hsub : Complex.measurableEquivRealProd.symm ⁻¹' (ball z r) ⊆ I ×ˢ J := by
    intro p hp
    have hn : ‖Complex.measurableEquivRealProd.symm p - z‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hp
    have hre := (Complex.abs_re_le_norm (Complex.measurableEquivRealProd.symm p - z)).trans
      (le_of_lt hn)
    have him := (Complex.abs_im_le_norm (Complex.measurableEquivRealProd.symm p - z)).trans
      (le_of_lt hn)
    change |p.1 - z.re| ≤ r at hre
    change |p.2 - z.im| ≤ r at him
    have hre' := abs_le.mp hre
    have him' := abs_le.mp him
    dsimp [I, J]
    constructor <;> constructor <;> linarith
  have hI : gaussianReal 0 v I ≤ ENNReal.ofReal (2 * r / Real.sqrt (2 * Real.pi * v)) := by
    have h := LatticeProb.gaussianReal_Icc_le hv (c := z.re - r) (d := z.re + r) (by linarith)
    simpa [I, show z.re + r - (z.re - r) = 2 * r by ring] using h
  have hJ : gaussianReal 0 v J ≤ ENNReal.ofReal (2 * r / Real.sqrt (2 * Real.pi * v)) := by
    have h := LatticeProb.gaussianReal_Icc_le hv (c := z.im - r) (d := z.im + r) (by linarith)
    simpa [J, show z.im + r - (z.im - r) = 2 * r by ring] using h
  rw [planarGaussian, Complex.zero_re, Complex.zero_im,
    Measure.map_apply Complex.measurableEquivRealProd.symm.measurable isOpen_ball.measurableSet]
  calc
    _ ≤ ((gaussianReal 0 v).prod (gaussianReal 0 v)) (I ×ˢ J) := measure_mono hsub
    _ = gaussianReal 0 v I * gaussianReal 0 v J := Measure.prod_prod _ _
    _ ≤ (ENNReal.ofReal (2 * r / Real.sqrt (2 * Real.pi * v))) ^ 2 := by
      simpa [pow_two] using mul_le_mul' hI hJ

/-- Every planar Brownian increment satisfies a small-ball bound uniform in the centre. -/
theorem planarBrownianMotion_increment_smallBall_le_uniform_center (x z : ℂ)
    {s t : ℝ≥0} (hts : t ≠ s) {r : ℝ} (hr : 0 ≤ r) :
    planarBrownianMotion x {b | ‖b t - b s - z‖ < r} ≤
      min 1 ((ENNReal.ofReal (2 * r / Real.sqrt (2 * Real.pi *
        (nndist (t : ℝ) (s : ℝ) : ℝ)))) ^ 2) := by
  have hv : nndist (t : ℝ) (s : ℝ) ≠ 0 := by
    intro hzero
    apply hts
    exact_mod_cast (nndist_eq_zero.mp hzero)
  apply le_min
  · exact prob_le_one
  · have hm : Measurable (fun b : ContinuousPath ℂ => b t - b s) :=
      (ContinuousPath.measurable_coordinateProcess _).sub
        (ContinuousPath.measurable_coordinateProcess _)
    have h := congrArg (fun μ : Measure ℂ => μ (ball z r))
      (planarBrownianMotion_map_increment x s t)
    rw [Measure.map_apply hm isOpen_ball.measurableSet] at h
    have hh : planarBrownianMotion x {b | ‖b t - b s - z‖ < r} =
        planarGaussian 0 (nndist (t : ℝ) (s : ℝ)) (ball z r) := by
      simpa only [Metric.ball, Set.preimage_ofPred_eq, dist_eq_norm] using h
    rw [hh]
    exact planarGaussian_ball_le_uniform_center hv z hr

end HarmonicBalls
