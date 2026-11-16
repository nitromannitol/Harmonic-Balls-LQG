import HarmonicBalls.Proofs.Potential.Fundamental
import HarmonicBalls.Proofs.Potential.GreenPoleL1Continuity
import HarmonicBalls.Proofs.Potential.GreenGeneralIdentification
import HarmonicBalls.Proofs.Sec6.BoundedHarmonicExit
import Mathlib.Topology.TietzeExtension
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import HarmonicBalls.Proofs.Sec6.PlanarBrownianGenerator
import HarmonicBalls.Proofs.Sec6.StoppedPotentialIntegrability
import HarmonicBalls.Proofs.Sec3.ConservationOfMassStep3
import MarkovProcess.Trajectory.DynkinStopping
import MarkovProcess.Trajectory.ExpectedExitTime
import MarkovProcess.Trajectory.FeynmanKacFunctional
import MarkovProcess.Killed.ExitTimeIdentification
import MarkovProcess.Killed.GluingPotential

/-! # Brownian occupation and the logarithmic potential

For a bounded open planar set and a smooth compactly supported test function, the
expected Brownian occupation integral is twice the difference between its
logarithmic potential at the starting point and its expected value at exit.

Adapted from `MatedCRT.FirstPass.Derived.LogarithmicPotential`,
`MatedCRT.FirstPass.Derived.PlanarBrownianExitDynkin`, and
`MatedCRT.FirstPass.Derived.PlanarBrownianPoissonExit` in IDLA-Mated-CRT.
-/

open MeasureTheory Set Filter InnerProductSpace Laplacian ContinuousLinearMap MarkovProcess
  HarmonicBalls HarmonicBalls.Section6
open scoped ContDiff Convolution ENNReal NNReal Topology ZeroAtInfty

namespace HarmonicBalls.GreenOccupation

/-- The **logarithmic potential** `U g (x) = ∫ N(x, y) g(y) dy` of `g : ℂ → ℝ`, with the Newtonian kernel
`N(x, y) = -(2π)⁻¹ log |x - y|` of the plane. -/
noncomputable def logPotential (g : ℂ → ℝ) (x : ℂ) : ℝ :=
  ∫ y, HarmonicBalls.newtonKernel x y * g y

/-- The logarithmic potential is the convolution of the kernel `t ↦ N(0, t) = -(2π)⁻¹ log |t|` with `g`. -/
theorem logPotential_eq_convolution (g : ℂ → ℝ) :
    logPotential g = HarmonicBalls.newtonKernel 0 ⋆[lsmul ℝ ℝ, volume] g := by
  funext x
  have h : ∫ t, HarmonicBalls.newtonKernel x (x - t) * g (x - t) =
      ∫ y, HarmonicBalls.newtonKernel x y * g y :=
    integral_sub_left_eq_self (f := fun y => HarmonicBalls.newtonKernel x y * g y) (μ := volume) x
  rw [convolution_lsmul, logPotential, ← h]
  congr 1
  funext t
  simp only [smul_eq_mul, HarmonicBalls.newtonKernel, sub_sub_cancel, zero_sub, norm_neg]

/-- The logarithmic potential of a `C^n` function with compact support is `C^n`. -/
theorem contDiff_logPotential {g : ℂ → ℝ} {n : ℕ∞} (hg : ContDiff ℝ n g) (hgc : HasCompactSupport g) :
    ContDiff ℝ n (logPotential g) := by
  rw [logPotential_eq_convolution]
  exact hgc.contDiff_convolution_right (lsmul ℝ ℝ) (HarmonicBalls.locallyIntegrable_newtonKernel 0) hg

/-- The directional derivatives of the logarithmic potential of a `C¹` function with compact support fall on the
function: `D(U g)(x) v = U (D g(·) v)(x)`. -/
theorem fderiv_logPotential_apply {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (x v : ℂ) :
    fderiv ℝ (logPotential g) x v = logPotential (fun y => fderiv ℝ g y v) x := by
  rw [logPotential_eq_convolution, logPotential_eq_convolution,
    (hgc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) (HarmonicBalls.locallyIntegrable_newtonKernel 0) hg x).fderiv]
  exact convolution_precompR_apply (lsmul ℝ ℝ) (HarmonicBalls.locallyIntegrable_newtonKernel 0)
    (hgc.fderiv (𝕜 := ℝ)) (hg.continuous_fderiv one_ne_zero) x v

/-- A directional derivative of a function with compact support has compact support. -/
theorem hasCompactSupport_fderiv_apply {g : ℂ → ℝ} (hgc : HasCompactSupport g) (v : ℂ) :
    HasCompactSupport (fun y => fderiv ℝ g y v) :=
  (hgc.fderiv (𝕜 := ℝ)).mono fun y hy h =>
    (Function.mem_support.1 hy) (by simp [h])

/-- **Poisson equation for the logarithmic potential.** For `g` of class `C²` with compact support,
`Δ (U g) = -g` everywhere. -/
theorem laplacian_logPotential {g : ℂ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (x : ℂ) :
    Δ (logPotential g) x = -g x := by
  have hu : ContDiff ℝ 2 (logPotential g) := by
    have := contDiff_logPotential (n := 2) (by exact_mod_cast hg) hgc
    exact_mod_cast this
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hgv : ∀ v : ℂ, ContDiff ℝ 1 (fun y => fderiv ℝ g y v) := fun v =>
    (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have h1 : ∀ v : ℂ, (fun z => fderiv ℝ (logPotential g) z v) = logPotential (fun y => fderiv ℝ g y v) :=
    fun v => funext fun z => fderiv_logPotential_apply hg1 hgc z v
  rw [laplacian_eq_fderiv_fderiv hu, h1 1, h1 Complex.I,
    fderiv_logPotential_apply (hgv 1) (hasCompactSupport_fderiv_apply hgc 1),
    fderiv_logPotential_apply (hgv Complex.I) (hasCompactSupport_fderiv_apply hgc Complex.I),
    logPotential_eq_convolution, logPotential_eq_convolution]
  have hex : ∀ v : ℂ, ConvolutionExistsAt (HarmonicBalls.newtonKernel 0)
      (fun y => fderiv ℝ (fun z => fderiv ℝ g z v) y v) x (lsmul ℝ ℝ) volume := fun v =>
    (hasCompactSupport_fderiv_apply (hasCompactSupport_fderiv_apply hgc v) v).convolutionExists_right
      (lsmul ℝ ℝ) (HarmonicBalls.locallyIntegrable_newtonKernel 0)
      (((hgv v).continuous_fderiv one_ne_zero).clm_apply continuous_const) x
  rw [← ConvolutionExistsAt.distrib_add (hex 1) (hex Complex.I)]
  have hΔ : (fun y => fderiv ℝ (fun z => fderiv ℝ g z 1) y 1) +
      (fun y => fderiv ℝ (fun z => fderiv ℝ g z Complex.I) y Complex.I) = Δ g := by
    funext y
    rw [Pi.add_apply, laplacian_eq_fderiv_fderiv hg]
  rw [hΔ, ← logPotential_eq_convolution, logPotential, integral_newtonKernel_mul_laplacian hg hgc]

/-- A smooth compactly supported function equal to `-‖y‖² / 2` near a bounded set; its Laplacian
is `-2` on that set. -/
theorem exists_contDiff_hasCompactSupport_laplacian_eq_neg_two {U : Set ℂ}
    (hUb : Bornology.IsBounded U) :
    ∃ g : ℂ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∀ x ∈ U, Δ g x = -2 := by
  obtain ⟨R, hR⟩ := hUb.subset_closedBall (0 : ℂ)
  let φ : ContDiffBump (0 : ℂ) := ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → ℝ, F = fun t ↦ (-1 / 2 : ℝ) * t := ⟨_, rfl⟩
  have hF : ContDiff ℝ ∞ F := hFdef ▸ contDiff_const.mul contDiff_id
  have hdF : deriv F = fun _ ↦ (-1 / 2 : ℝ) := by
    funext t
    have h : HasDerivAt F (-1 / 2 : ℝ) t := by
      rw [hFdef]
      simpa using (hasDerivAt_id t).const_mul (-1 / 2 : ℝ)
    exact h.deriv
  refine ⟨fun y ↦ φ y * F (‖y‖ ^ 2), φ.contDiff.mul (hF.comp (contDiff_norm_sq ℝ)),
    φ.hasCompactSupport.mul_right, fun x hx ↦ ?_⟩
  have hx' : x ∈ Metric.ball (0 : ℂ) (|R| + 1) := by
    have h := hR hx
    rw [Metric.mem_closedBall] at h
    rw [Metric.mem_ball]
    linarith [le_abs_self R]
  have heq : (fun y ↦ φ y * F (‖y‖ ^ 2)) =ᶠ[𝓝 x] fun y ↦ F (‖y‖ ^ 2) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx'] with y hy
    rw [φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), one_mul]
  rw [(laplacian_congr_nhds heq).eq_of_nhds, laplacian_comp_norm_sq hF, hdF]
  norm_num [deriv_const']

/-- **Finite mean exit time.** The exit time of planar Brownian motion from a bounded open set has
finite expectation from every starting point. -/
theorem lintegral_exitTime_planarBrownianMotion_lt_top {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (x : ℂ) :
    ∫⁻ p, ContinuousPath.exitTime D p ∂(planarBrownianMotion x) < ⊤ := by
  obtain ⟨g, hg, hgc, hΔ⟩ := exists_contDiff_hasCompactSupport_laplacian_eq_neg_two hDb
  obtain ⟨f, hfg, hgen⟩ := exists_planarBrownian_generator_eq_half_laplacian g hg hgc
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hLf : ∀ y ∈ D,
      (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) y ≤ -1 := by
    intro y hy
    rw [hgen y, hΔ y hy]
    norm_num
  have hm : ∀ y, -M ≤ (f : C₀(ℂ, ℝ)) y := by
    intro y
    rw [hfg y]
    exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using hM y)).1
  rw [planarBrownianMotion_eq_continuousProcess]
  exact lt_of_le_of_lt
    (isFellerKernelSemigroup_planarHeatSemigroup.lintegral_exitTime_le
      isConservative_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup f D hD hLf hm x)
    ENNReal.ofReal_lt_top

/-- **Dynkin's formula at the exit time of a bounded domain.** For a smooth compactly supported
`g` and a bounded open `D`, `E_x g(𝓑_{τ_D}) - g(x) = ½ E_x ∫_0^{τ_D} Δg(𝓑_s) ds`. -/
theorem planarBrownianMotion_exit_dynkin {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (x : ℂ) :
    (∫ p, g (p ((ContinuousPath.exitTime D p).toNNReal)) ∂(planarBrownianMotion x)) - g x =
      (1 / 2 : ℝ) * ∫ p, (∫ s in (0 : ℝ)..((ContinuousPath.exitTime D p).toNNReal : ℝ),
        Δ g (p s.toNNReal)) ∂(planarBrownianMotion x) := by
  obtain ⟨f, hfg, hgen⟩ := exists_planarBrownian_generator_eq_half_laplacian g hg hgc
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  obtain ⟨A, hA⟩ := (hasCompactSupport_laplacian hgc).exists_bound_of_continuous
    (continuous_laplacian_of_contDiff (hg.of_le (by norm_num)))
  have hbd (y : ℂ) : ‖(1 / 2 : ℝ) * Δ g y‖ ≤ A := by
    calc ‖(1 / 2 : ℝ) * Δ g y‖ = (1 / 2) * ‖Δ g y‖ := by
          rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      _ ≤ A := by linarith [hA y, norm_nonneg (Δ g y)]
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hbd 0)
  have hdyn (n : ℕ) :
      (∫ p, g (p (ContinuousPath.exitTimeTrunc D n p)) ∂(planarBrownianMotion x)) - g x =
        ∫ p, (∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc D n p : ℝ),
          (1 / 2 : ℝ) * Δ g (p s.toNNReal)) ∂(planarBrownianMotion x) := by
    have h := isFellerKernelSemigroup_planarHeatSemigroup.integral_eval_stoppingTime_sub_eq_integral_integral_generator
      isConservative_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup f
      (ContinuousPath.exitTimeTrunc D n) (ContinuousPath.isStoppingTime_exitTimeTrunc D hD n)
      (ContinuousPath.exitTimeTrunc_le D n) x
    rw [← planarBrownianMotion_eq_continuousProcess] at h
    simpa only [hfg, hgen] using h
  have hint (n : ℕ) : Integrable (fun p : ContinuousPath ℂ ↦
      ∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc D n p : ℝ),
        (1 / 2 : ℝ) * Δ g (p s.toNNReal)) (planarBrownianMotion x) := by
    have h := isFellerKernelSemigroup_planarHeatSemigroup.integrable_integral_generator_stoppingTime
      isConservative_planarHeatSemigroup f
      (ContinuousPath.exitTimeTrunc D n) (ContinuousPath.isStoppingTime_exitTimeTrunc D hD n)
      (ContinuousPath.exitTimeTrunc_le D n) x
    rw [← planarBrownianMotion_eq_continuousProcess] at h
    simpa only [hgen] using h
  have hfin := ae_planarBrownian_exitTime_bounded_lt_top x hDb
  have hτ := lintegral_exitTime_planarBrownianMotion_lt_top hD hDb x
  have hRHS : Tendsto (fun n : ℕ ↦ ∫ p, (∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc D n p : ℝ),
        (1 / 2 : ℝ) * Δ g (p s.toNNReal)) ∂(planarBrownianMotion x)) atTop
      (𝓝 (∫ p, (∫ s in (0 : ℝ)..((ContinuousPath.exitTime D p).toNNReal : ℝ),
        (1 / 2 : ℝ) * Δ g (p s.toNNReal)) ∂(planarBrownianMotion x))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun p ↦ A * (ContinuousPath.exitTime D p).toReal) (fun n ↦ (hint n).aestronglyMeasurable)
      ((integrable_toReal_of_lintegral_ne_top
        (ContinuousPath.measurable_exitTime D hD).aemeasurable hτ.ne).const_mul A) ?_ ?_
    · intro n
      filter_upwards [hfin] with p hp
      have hle : (ContinuousPath.exitTimeTrunc D n p : ℝ≥0∞) ≤ ContinuousPath.exitTime D p := by
        rw [ContinuousPath.coe_exitTimeTrunc_ennreal]
        exact min_le_left _ _
      have hle' : ContinuousPath.exitTimeTrunc D n p ≤ (ContinuousPath.exitTime D p).toNNReal := by
        have h := ENNReal.toNNReal_mono hp.ne hle
        rwa [ENNReal.toNNReal_coe] at h
      have hb : ∀ s ∈ Set.uIoc (0 : ℝ) (ContinuousPath.exitTimeTrunc D n p : ℝ),
          ‖(1 / 2 : ℝ) * Δ g (p s.toNNReal)‖ ≤ A := fun s _ ↦ hbd _
      calc ‖∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc D n p : ℝ),
            (1 / 2 : ℝ) * Δ g (p s.toNNReal)‖
          ≤ A * |(ContinuousPath.exitTimeTrunc D n p : ℝ) - 0| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hb
        _ ≤ A * (ContinuousPath.exitTime D p).toReal := by
            rw [sub_zero, abs_of_nonneg (NNReal.coe_nonneg _), ← ENNReal.coe_toNNReal_eq_toReal]
            exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hle') hA0
    · filter_upwards [hfin] with p hp
      obtain ⟨N, hN⟩ := exists_nat_ge (ContinuousPath.exitTime D p).toNNReal
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      have ht : ContinuousPath.exitTimeTrunc D n p = (ContinuousPath.exitTime D p).toNNReal := by
        apply ENNReal.coe_injective
        have hle' : ContinuousPath.exitTime D p ≤ ((n : ℝ≥0) : ℝ≥0∞) := by
          rw [← ENNReal.coe_toNNReal hp.ne, ENNReal.coe_le_coe]
          exact hN.trans (by exact_mod_cast hn)
        rw [ContinuousPath.coe_exitTimeTrunc_ennreal, min_eq_left hle', ENNReal.coe_toNNReal hp.ne]
      rw [ht]
  have hLHS := (tendsto_integral_exitTimeTrunc_of_bounded_measurable hD hDb hg.continuous.measurable
    hM x).sub_const (g x)
  rw [tendsto_nhds_unique (hLHS.congr hdyn) hRHS]
  simp only [intervalIntegral.integral_const_mul, integral_const_mul]

/-- **Expected occupation integral before exit.** For a bounded open `D`, `y ∈ D` and a smooth
compactly supported `g`, `E_y ∫_0^{τ_D} g(𝓑_s) ds = 2 (U g(y) - E_y U g(𝓑_{τ_D}))`, where `U g` is
the logarithmic potential of `g`. -/
theorem integral_occupation_exitTime_eq_logPotential {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    {y : ℂ} (hy : y ∈ D) :
    ∫ p, (∫ s in (0 : ℝ)..((ContinuousPath.exitTime D p).toNNReal : ℝ), g (p s.toNNReal))
        ∂(planarBrownianMotion y) =
      2 * (logPotential g y - ∫ p, logPotential g (p ((ContinuousPath.exitTime D p).toNNReal))
        ∂(planarBrownianMotion y)) := by
  obtain ⟨R, hR⟩ := hDb.subset_closedBall (0 : ℂ)
  let χ : ContDiffBump (0 : ℂ) := ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  have hU : ContDiff ℝ ∞ (logPotential g) := contDiff_logPotential hg hgc
  have hclD : closure D ⊆ Metric.ball (0 : ℂ) (|R| + 1) := by
    refine (closure_minimal hR Metric.isClosed_closedBall).trans ?_
    intro w hw
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    linarith [le_abs_self R]
  have hfeq : ∀ w ∈ Metric.ball (0 : ℂ) (|R| + 1), χ w * logPotential g w = logPotential g w := by
    intro w hw
    rw [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hw), one_mul]
  have hΔ : ∀ w ∈ Metric.ball (0 : ℂ) (|R| + 1),
      Δ (fun v ↦ χ v * logPotential g v) w = -g w := by
    intro w hw
    have heq : (fun v ↦ χ v * logPotential g v) =ᶠ[𝓝 w] logPotential g := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hw] with v hv
      exact hfeq v hv
    rw [(laplacian_congr_nhds heq).eq_of_nhds,
      laplacian_logPotential (hg.of_le (by norm_num)) hgc]
  have hdyn := planarBrownianMotion_exit_dynkin hD hDb (χ.contDiff.mul hU)
    χ.hasCompactSupport.mul_right y
  beta_reduce at hdyn
  have hend : ∫ p, χ (p ((ContinuousPath.exitTime D p).toNNReal)) *
        logPotential g (p ((ContinuousPath.exitTime D p).toNNReal)) ∂(planarBrownianMotion y) =
      ∫ p, logPotential g (p ((ContinuousPath.exitTime D p).toNNReal))
        ∂(planarBrownianMotion y) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_planarBrownianMotion_eval_zero y,
      ae_planarBrownian_exitTime_bounded_lt_top y hDb] with p h0 hfin
    have h0D : p 0 ∈ D := by rw [h0]; exact hy
    have hmem := ContinuousPath.coordinate_exitTime_mem_frontier D hD p h0D hfin.ne
    exact hfeq _ (hclD (frontier_subset_closure hmem))
  have hdrift : ∀ p : ContinuousPath ℂ,
      (∫ s in (0 : ℝ)..((ContinuousPath.exitTime D p).toNNReal : ℝ),
        Δ (fun v ↦ χ v * logPotential g v) (p s.toNNReal)) =
      -∫ s in (0 : ℝ)..((ContinuousPath.exitTime D p).toNNReal : ℝ), g (p s.toNNReal) := by
    intro p
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_ae ?_
    have hsingle : ∀ᵐ s : ℝ, s ≠ ((ContinuousPath.exitTime D p).toNNReal : ℝ) := by
      rw [ae_iff]
      simpa only [Ne, not_not, Set.ofPred_eq_eq_singleton] using
        measure_singleton (((ContinuousPath.exitTime D p).toNNReal : ℝ))
    filter_upwards [hsingle] with s hs hmem
    rw [Set.uIoc_of_le (NNReal.coe_nonneg _)] at hmem
    have hlt : s.toNNReal < (ContinuousPath.exitTime D p).toNNReal :=
      (Real.toNNReal_lt_iff_lt_coe hmem.1.le).mpr (lt_of_le_of_ne hmem.2 hs)
    have hpD : p s.toNNReal ∈ D := ContinuousPath.mem_of_lt_exitTime D p _
      (lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr hlt) ENNReal.coe_toNNReal_le_self)
    exact hΔ _ (hclD (subset_closure hpD))
  rw [hend, hfeq y (hclD (subset_closure hy))] at hdyn
  simp only [hdrift, integral_neg] at hdyn
  linarith [hdyn]

/-- A function harmonic in a bounded open set and continuous on its closure is
represented by its values at the Brownian exit point. -/
theorem harmonic_eq_integral_exitTime_of_continuousOn_closure
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    {q : ℂ → ℝ} (hq : ContinuousOn q (closure D)) (hharm : HarmonicOnNhd q D)
    {x : ℂ} (hx : x ∈ D) :
    q x = ∫ p : ContinuousPath ℂ,
      q (p ((ContinuousPath.exitTime D p).toNNReal)) ∂(planarBrownianMotion x) := by
  let : CompactSpace (closure D) := isCompact_iff_compactSpace.mp hDb.isCompact_closure
  let f : C(closure D, ℝ) := ⟨fun z => q z, hq.domRestrict⟩
  let fb : BoundedContinuousFunction (closure D) ℝ := BoundedContinuousFunction.mkOfCompact f
  obtain ⟨g, -, hg⟩ := fb.exists_norm_eq_domRestrict_eq_of_closed isClosed_closure
  have heq : ∀ z ∈ closure D, g z = q z := by
    intro z hz
    have h := congrArg (fun k : BoundedContinuousFunction (closure D) ℝ => k ⟨z, hz⟩) hg
    exact h
  have hgh : HarmonicOnNhd g D := by
    intro z hz
    apply (harmonicAt_congr_nhds ?_).2 (hharm z hz)
    filter_upwards [hD.mem_nhds hz] with w hw
    exact heq w (subset_closure hw)
  have hrep := harmonic_eq_integral_planarBrownian_exitTime hD hDb g.continuous hgh
    (fun z => g.norm_coe_le_norm z) hx
  rw [heq x (subset_closure hx)] at hrep
  refine hrep.trans (integral_congr_ae ?_)
  filter_upwards [ae_planarBrownianMotion_eval_zero x,
    ae_planarBrownian_exitTime_bounded_lt_top x hDb] with p h0 hfin
  have hstart : p 0 ∈ D := by rw [h0]; exact hx
  exact heq _ (frontier_subset_closure
    (ContinuousPath.coordinate_exitTime_mem_frontier D hD p hstart hfin.ne))

/-- The occupation identity for smooth tests supported in a smooth bounded
open domain. The factor two corresponds to the standard Brownian generator
`Δ / 2`. -/
theorem integral_occupation_exitTime_eq_greenPotential
    {D : Set ℂ} (hD : IsSmoothBoundedOpen D) {g : ℂ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgs : Function.support g ⊆ D) {x : ℂ} (hx : x ∈ D) :
    ∫ p, (∫ s in (0 : ℝ)..((ContinuousPath.exitTime D p).toNNReal : ℝ), g (p s.toNNReal))
        ∂(planarBrownianMotion x) =
      2 * ∫ y in D, greenFunction D x y * g y := by
  have hDo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  have hDb := hD.1
  obtain ⟨r, hr⟩ := hDb.subset_ball (0 : ℂ)
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hDR : D ⊆ Metric.ball (0 : ℂ) R := hr.trans (Metric.ball_subset_ball (le_max_left _ _))
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hM' : ∀ᵐ y ∂(volume.restrict D), |g y| ≤ M :=
    ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using hM y)
  have hmeas : AEStronglyMeasurable g (volume.restrict D) :=
    hg.continuous.stronglyMeasurable.aestronglyMeasurable
  have hrestrict : ∀ z, (∫ y in D, newtonKernel z y * g y) = logPotential g z := by
    intro z
    rw [← integral_indicator hDo.measurableSet, logPotential]
    congr 1
    funext y
    by_cases hy : y ∈ D
    · simp only [indicator_of_mem hy]
    · have hzero : g y = 0 := by
        by_contra hn
        exact hy (hgs hn)
      simp only [indicator_of_notMem hy, hzero, mul_zero]
  have hcont : ContinuousOn (fun z => logPotential g z -
      ∫ y in D, greenFunction D z y * g y) (closure D) :=
    (contDiff_logPotential hg hgc).continuous.continuousOn.sub
      (GreenGeneral.VolumeGrowth.continuousOn_greenPotential hR (volumeGrowth_volume R) hD hDR hmeas hM')
  have hharm : HarmonicOnNhd (fun z => logPotential g z -
      ∫ y in D, greenFunction D z y * g y) D := by
    have h := GreenGeneral.VolumeGrowth.harmonicOnNhd_newtonPotential_sub_greenPotential
      hR (volumeGrowth_volume R) hD hDR hmeas hM'
    simpa only [hrestrict] using h
  have hrep := harmonic_eq_integral_exitTime_of_continuousOn_closure hDo hDb hcont hharm hx
  have hexit : (∫ p : ContinuousPath ℂ,
      (logPotential g (p ((ContinuousPath.exitTime D p).toNNReal)) -
        ∫ y in D, greenFunction D (p ((ContinuousPath.exitTime D p).toNNReal)) y * g y)
        ∂(planarBrownianMotion x)) =
      ∫ p : ContinuousPath ℂ, logPotential g (p ((ContinuousPath.exitTime D p).toNNReal))
        ∂(planarBrownianMotion x) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_planarBrownianMotion_eval_zero x,
      ae_planarBrownian_exitTime_bounded_lt_top x hDb] with p h0 hfin
    have hstart : p 0 ∈ D := by rw [h0]; exact hx
    have hfront := ContinuousPath.coordinate_exitTime_mem_frontier D hDo p hstart hfin.ne
    have hnot : p ((ContinuousPath.exitTime D p).toNNReal) ∉ D := by
      rw [hDo.frontier_eq] at hfront
      exact hfront.2
    simp only [greenFunction_of_notMem_left hnot, zero_mul, integral_zero, sub_zero]
  rw [hexit] at hrep
  rw [integral_occupation_exitTime_eq_logPotential hDo hDb hg hgc hx]
  linarith

/-- The total mass of the zero-shift killed resolvent is finite on bounded
open sets. -/
theorem killedResolvent_zero_one_lt_top {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (x : ℂ) :
    SubMarkovKernelSemigroup.IsConservative.killedResolvent
      planarHeatSemigroup isConservative_planarHeatSemigroup D hD 0 (fun _ => 1) x < ⊤ := by
  rw [← SubMarkovKernelSemigroup.IsConservative.lintegral_exitTime_eq_killedResolvent_zero
    planarHeatSemigroup isConservative_planarHeatSemigroup D hD x,
    ← planarBrownianMotion_eq_continuousProcess]
  exact lintegral_exitTime_planarBrownianMotion_lt_top hD hDb x

/-- The zero-shift killed potential is the expected occupation measure. -/
noncomputable def occupationMeasure (D : Set ℂ) (hD : IsOpen D) (x : ℂ) : Measure ℂ :=
  SubMarkovKernelSemigroup.IsConservative.killedPotential
    planarHeatSemigroup isConservative_planarHeatSemigroup D hD 0 x

/-- The occupation measure has finite total mass for bounded open sets. -/
theorem isFiniteMeasure_occupationMeasure {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (x : ℂ) : IsFiniteMeasure (occupationMeasure D hD x) := by
  refine ⟨?_⟩
  rw [← lintegral_one, occupationMeasure,
    SubMarkovKernelSemigroup.IsConservative.lintegral_killedPotential _ _ _ _ _ measurable_const]
  exact killedResolvent_zero_one_lt_top hD hDb x

/-- Nonnegative measurable observables of the occupation measure are given by
integration along the source Brownian paths before exit. -/
theorem lintegral_occupationMeasure {D : Set ℂ} (hD : IsOpen D) (x : ℂ)
    {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂occupationMeasure D hD x =
      ∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ),
        {t : ℝ | ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D p}.indicator
          (fun t => f (p (Real.toNNReal t))) t) ∂(planarBrownianMotion x) := by
  rw [occupationMeasure,
    SubMarkovKernelSemigroup.IsConservative.lintegral_killedPotential _ _ _ _ _ hf,
    SubMarkovKernelSemigroup.IsConservative.killedResolvent_eq_lintegral _ _ _ _ _ hf,
    ← planarBrownianMotion_eq_continuousProcess]
  simp only [zero_mul, neg_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul]

/-- For a finite exit time, the nonnegative time integral along a continuous path
is the extended-real image of its real stopped integral. -/
theorem lintegral_before_exit_eq_ofReal_intervalIntegral (D : Set ℂ) (p : ContinuousPath ℂ) {g : ℂ → ℝ}
    (hg : Continuous g) (hg0 : ∀ y, 0 ≤ g y)
    (hfin : ContinuousPath.exitTime D p ≠ ⊤) :
    (∫⁻ t in Set.Ioi (0 : ℝ),
      {t : ℝ | ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D p}.indicator
        (fun t => ENNReal.ofReal (g (p (Real.toNNReal t)))) t) =
      ENNReal.ofReal (∫ t in (0 : ℝ)..((ContinuousPath.exitTime D p).toNNReal : ℝ),
        g (p (Real.toNNReal t))) := by
  let τ := ContinuousPath.exitTime D p
  have hS : MeasurableSet {t : ℝ | ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) < τ} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp measurable_real_toNNReal) measurable_const
  rw [lintegral_indicator hS, Measure.restrict_restrict hS, ContinuousPath.survivalSet τ,
    ite_eq_right hfin]
  have hcont : Continuous (fun t : ℝ => g (p (Real.toNNReal t))) :=
    hg.comp (p.continuous.comp continuous_real_toNNReal)
  have ht : (0 : ℝ) ≤ (τ.toNNReal : ℝ) := NNReal.coe_nonneg _
  have hi : IntegrableOn (fun t : ℝ => g (p (Real.toNNReal t))) (Ioc 0 (τ.toNNReal : ℝ)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp (hcont.intervalIntegrable _ _)
  rw [intervalIntegral.integral_of_le ht,
    ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => hg0 _)]
  congr 1
  rw [← ENNReal.coe_toNNReal_eq_toReal]
  exact restrict_Ioo_eq_restrict_Ioc

/-- The occupation measure integrates a nonnegative continuous observable as
the expected extended-real image of its stopped path integral. -/
theorem lintegral_occupationMeasure_eq_stopped_integral {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (x : ℂ) {g : ℂ → ℝ} (hg : Continuous g)
    (hg0 : ∀ y, 0 ≤ g y) :
    ∫⁻ y, ENNReal.ofReal (g y) ∂occupationMeasure D hD x =
      ∫⁻ p, ENNReal.ofReal (∫ t in (0 : ℝ)..((ContinuousPath.exitTime D p).toNNReal : ℝ),
        g (p (Real.toNNReal t))) ∂(planarBrownianMotion x) := by
  rw [lintegral_occupationMeasure hD x hg.measurable.ennreal_ofReal]
  apply lintegral_congr_ae
  filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top x hDb] with p hfin
  exact lintegral_before_exit_eq_ofReal_intervalIntegral D p hg hg0 hfin.ne

/-- Integration of a nonnegative continuous observable against the occupation
measure equals its expected stopped path integral. -/
theorem integral_occupationMeasure_eq_stopped_integral {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (x : ℂ) {g : ℂ → ℝ} (hg : Continuous g)
    (hg0 : ∀ y, 0 ≤ g y) :
    ∫ y, g y ∂occupationMeasure D hD x =
      ∫ p, (∫ t in (0 : ℝ)..((ContinuousPath.exitTime D p).toNNReal : ℝ),
        g (p (Real.toNNReal t))) ∂(planarBrownianMotion x) := by
  have hm : Measurable (fun p : ContinuousPath ℂ =>
      ∫ t in (0 : ℝ)..((ContinuousPath.exitTime D p).toNNReal : ℝ),
        g (p (Real.toNNReal t))) := by
    exact (SubMarkovKernelSemigroup.stronglyMeasurable_feynmanKacAdditiveFunctional_joint hg.measurable).measurable.comp
      ((ContinuousPath.measurable_exitTime D hD).ennreal_toNNReal.prodMk measurable_id)
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0)
    hg.stronglyMeasurable.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun p =>
      intervalIntegral.integral_nonneg_of_forall (NNReal.coe_nonneg _) (fun _ => hg0 _))
      hm.stronglyMeasurable.aestronglyMeasurable,
    lintegral_occupationMeasure_eq_stopped_integral hD hDb x hg hg0]

/-- The occupation measure assigns zero mass to the complement of the domain. -/
theorem occupationMeasure_compl {D : Set ℂ} (hD : IsOpen D) (x : ℂ) :
    occupationMeasure D hD x Dᶜ = 0 := by
  rw [← lintegral_indicator_one hD.measurableSet.compl]
  change (∫⁻ y, Dᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y ∂occupationMeasure D hD x) = 0
  rw [lintegral_occupationMeasure hD x (measurable_const.indicator hD.measurableSet.compl)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [] with p
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [] with t
  by_cases ht : ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D p
  · have hp := ContinuousPath.mem_of_lt_exitTime D p (Real.toNNReal t) ht
    simp [ht, hp]
  · simp [ht]

/-- The measure with density twice the zero-extended Green function. -/
noncomputable def greenMeasure (D : Set ℂ) (x : ℂ) : Measure ℂ :=
  volume.withDensity (fun y => ENNReal.ofReal (2 * greenFunction D x y))

/-- The Green measure is absolutely continuous with respect to planar volume. -/
theorem greenMeasure_absolutelyContinuous (D : Set ℂ) (x : ℂ) :
    greenMeasure D x ≪ volume :=
  withDensity_absolutelyContinuous volume _

/-- Changing the density at the pole leaves the Green measure unchanged. -/
theorem greenMeasure_eq_withDensity_of_eq_off_pole (D : Set ℂ) (x : ℂ)
    {f : ℂ → ℝ≥0∞} (hf : ∀ y, y ≠ x → f y = ENNReal.ofReal (2 * greenFunction D x y)) :
    greenMeasure D x = volume.withDensity f := by
  apply withDensity_congr_ae
  filter_upwards [show ∀ᵐ y : ℂ, y ≠ x by
    rw [ae_iff]
    simpa only [Ne, not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton x)] with y hy
  exact (hf y hy).symm

/-- The Green measure gives no mass to individual points. -/
theorem greenMeasure_singleton (D : Set ℂ) (x y : ℂ) : greenMeasure D x {y} = 0 :=
  greenMeasure_absolutelyContinuous D x (measure_singleton y)

/-- The Green measure is concentrated on the domain. -/
theorem greenMeasure_compl {D : Set ℂ} (hD : IsOpen D) (x : ℂ) :
    greenMeasure D x Dᶜ = 0 := by
  rw [greenMeasure, withDensity_apply _ hD.measurableSet.compl]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem hD.measurableSet.compl] with y hy
  simp only [greenFunction_of_notMem_right hy, mul_zero, ENNReal.ofReal_zero, Pi.zero_apply]

/-- The Green density is integrable on bounded open domains. -/
theorem isFiniteMeasure_greenMeasure {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (x : ℂ) : IsFiniteMeasure (greenMeasure D x) := by
  exact isFiniteMeasure_withDensity_ofReal
    ((integrable_greenFunction_pole hD hDb x).const_mul 2).2

/-- Integration against the Green measure uses the normalization `2 G_D`. -/
theorem integral_greenMeasure {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (x : ℂ) (g : ℂ → ℝ) :
    ∫ y, g y ∂greenMeasure D x = 2 * ∫ y in D, greenFunction D x y * g y := by
  have hmeas : AEMeasurable (fun y => ENNReal.ofReal (2 * greenFunction D x y)) volume :=
    ((integrable_greenFunction_pole hD hDb x).const_mul 2).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [greenMeasure, integral_withDensity_eq_integral_toReal_smul₀ hmeas
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ← integral_indicator hD.measurableSet, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ D
  · rw [ENNReal.toReal_ofReal (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (greenFunction_nonneg hDb x y))]
    simp [hy, smul_eq_mul, mul_assoc]
  · simp [hy, greenFunction_of_notMem_right hy]

/-- Smooth tests of the Green measure equal expected occupation before exit. -/
theorem integral_greenMeasure_eq_occupation {D : Set ℂ} (hD : IsSmoothBoundedOpen D)
    {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgs : Function.support g ⊆ D) {x : ℂ} (hx : x ∈ D) :
    ∫ y, g y ∂greenMeasure D x =
      ∫ p, (∫ s in (0 : ℝ)..((ContinuousPath.exitTime D p).toNNReal : ℝ), g (p s.toNNReal))
        ∂(planarBrownianMotion x) := by
  rw [integral_greenMeasure (GreenGeneral.isOpen_of_isSmoothBoundedOpen hD) hD.1,
    integral_occupation_exitTime_eq_greenPotential hD hg hgc hgs hx]

/-- The occupation and Green measures agree on nonnegative smooth tests
supported in the domain. -/
theorem integral_occupationMeasure_eq_integral_greenMeasure
    {D : Set ℂ} (hD : IsSmoothBoundedOpen D) {g : ℂ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgs : Function.support g ⊆ D) (hg0 : ∀ y, 0 ≤ g y) {x : ℂ} (hx : x ∈ D) :
    ∫ y, g y ∂occupationMeasure D (GreenGeneral.isOpen_of_isSmoothBoundedOpen hD) x =
      ∫ y, g y ∂greenMeasure D x := by
  rw [integral_occupationMeasure_eq_stopped_integral _ hD.1 x hg.continuous hg0,
    integral_greenMeasure_eq_occupation hD hg hgc hgs hx]

/-- Equality on nonnegative smooth compactly supported tests extends to
nonnegative continuous compactly supported tests with the same support restriction. -/
theorem integral_eq_of_nonneg_continuous_tests (D : Set ℂ) (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (htest : ∀ g : ℂ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      Function.support g ⊆ D → (∀ y, 0 ≤ g y) → ∫ y, g y ∂μ = ∫ y, g y ∂ν)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfs : Function.support f ⊆ D) (hf0 : ∀ y, 0 ≤ f y) :
    ∫ y, f y ∂μ = ∫ y, f y ∂ν := by
  have hsqrt : Continuous (fun y => Real.sqrt (f y)) := Real.continuous_sqrt.comp hf
  have hsupp : Function.support (fun y => Real.sqrt (f y)) ⊆ Function.support f := by
    intro y hy
    contrapose! hy
    simp only [Function.mem_support, not_ne_iff] at hy ⊢
    rw [hy, Real.sqrt_zero]
  have hsqrtc : HasCompactSupport (fun y => Real.sqrt (f y)) := hfc.mono hsupp
  choose g hg hdist hgs using fun n : ℕ =>
    hsqrt.exists_contDiff_approx (⊤ : ℕ∞) (ε := fun _ => (1 : ℝ) / (n + 1))
      continuous_const (by intro; positivity)
  let G : ℕ → ℂ → ℝ := fun n y => (g n y) ^ 2
  have hGc (n : ℕ) : ContDiff ℝ ∞ (G n) := (hg n).pow 2
  have hGsupport (n : ℕ) : Function.support (G n) ⊆ Function.support f := by
    intro y hy
    apply hsupp (hgs n ?_)
    intro hz
    exact hy (by change (g n y)^2 = 0; rw [hz]; norm_num)
  have hGcompact (n : ℕ) : HasCompactSupport (G n) := hfc.mono (hGsupport n)
  have heq (n : ℕ) : ∫ y, G n y ∂μ = ∫ y, G n y ∂ν :=
    htest (G n) (hGc n) (hGcompact n) ((hGsupport n).trans hfs) (fun y => sq_nonneg _)
  obtain ⟨M, hM⟩ := hsqrtc.exists_bound_of_continuous hsqrt
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hbound (n : ℕ) (y : ℂ) : ‖G n y‖ ≤ (M + 1)^2 := by
    have hd : ‖g n y - Real.sqrt (f y)‖ < 1 := by
      have h := hdist n y
      rw [Real.dist_eq] at h
      rw [Real.norm_eq_abs]
      calc |g n y - Real.sqrt (f y)| < 1 / ((n : ℝ) + 1) := h
        _ ≤ 1 := by
          exact (div_le_one₀ (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hb : ‖g n y‖ ≤ M + 1 := by
      have := norm_add_le (g n y - Real.sqrt (f y)) (Real.sqrt (f y))
      have : ‖g n y‖ ≤ ‖g n y - Real.sqrt (f y)‖ + ‖Real.sqrt (f y)‖ := by simpa using this
      linarith [hM y]
    simp only [G, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hlim (y : ℂ) : Tendsto (fun n => G n y) atTop (𝓝 (f y)) := by
    have hsmall : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) := by
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hgconv : Tendsto (fun n => g n y) atTop (𝓝 (Real.sqrt (f y))) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      refine squeeze_zero (fun n => dist_nonneg) (fun n => (hdist n y).le) hsmall
    simpa [G, Real.sq_sqrt (hf0 y)] using hgconv.pow 2
  have hμ := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (M + 1)^2)
    (fun n => (hGc n).continuous.stronglyMeasurable.aestronglyMeasurable)
    (integrable_const _) (fun n => Eventually.of_forall (hbound n)) (Eventually.of_forall hlim)
  have hν := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ => (M + 1)^2)
    (fun n => (hGc n).continuous.stronglyMeasurable.aestronglyMeasurable)
    (integrable_const _) (fun n => Eventually.of_forall (hbound n)) (Eventually.of_forall hlim)
  exact tendsto_nhds_unique (hμ.congr (fun n => heq n)) hν

/-- The occupation and Green measures agree on nonnegative continuous compactly
supported tests supported in the domain. -/
theorem integral_occupationMeasure_eq_integral_greenMeasure_of_continuous
    {D : Set ℂ} (hD : IsSmoothBoundedOpen D) {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfs : Function.support f ⊆ D)
    (hf0 : ∀ y, 0 ≤ f y) {x : ℂ} (hx : x ∈ D) :
    ∫ y, f y ∂occupationMeasure D (GreenGeneral.isOpen_of_isSmoothBoundedOpen hD) x =
      ∫ y, f y ∂greenMeasure D x := by
  let hDo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  let : IsFiniteMeasure (occupationMeasure D hDo x) := isFiniteMeasure_occupationMeasure hDo hD.1 x
  let : IsFiniteMeasure (greenMeasure D x) := isFiniteMeasure_greenMeasure hDo hD.1 x
  exact integral_eq_of_nonneg_continuous_tests D _ _
    (fun g hg hgc hgs hg0 => integral_occupationMeasure_eq_integral_greenMeasure
      hD hg hgc hgs hg0 hx) hf hfc hfs hf0

/-- Finite measures concentrated on an open set are determined by nonnegative
continuous compactly supported tests supported in that set. -/
theorem measure_eq_of_nonneg_continuous_tests {D : Set ℂ} (hD : IsOpen D) (μ ν : Measure ℂ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμD : μ Dᶜ = 0) (hνD : ν Dᶜ = 0)
    (htest : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Function.support f ⊆ D → (∀ y, 0 ≤ f y) → ∫ y, f y ∂μ = ∫ y, f y ∂ν) : μ = ν := by
  obtain ⟨ρ, hρsupp, hρsmooth, hρrange⟩ := hD.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  have hρ0 (y : ℂ) : 0 ≤ ρ y := (hρrange ⟨y, rfl⟩).1
  have hρpos {y : ℂ} (hy : y ∈ D) : 0 < ρ y := by
    have hn : ρ y ≠ 0 := by
      have : y ∈ Function.support ρ := hρsupp.symm ▸ hy
      exact this
    exact lt_of_le_of_ne (hρ0 y) (Ne.symm hn)
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro f
  let F : ℂ → ℝ := fun y => f y
  have hF : Continuous F := NNReal.continuous_coe.comp f.continuous
  have hFc : HasCompactSupport F := f.hasCompactSupport'.mono (by
    intro y hy
    change (f y : ℝ) ≠ 0 at hy
    change f y ≠ 0
    exact fun h => hy (by rw [h]; rfl))
  let w : ℕ → ℂ → ℝ := fun n y => min 1 ((n : ℝ) * ρ y)
  let G : ℕ → ℂ → ℝ := fun n y => F y * w n y
  have hw (n : ℕ) : Continuous (w n) := continuous_const.min (continuous_const.mul hρsmooth.continuous)
  have hw0 (n : ℕ) (y : ℂ) : 0 ≤ w n y := le_min (by norm_num) (mul_nonneg (Nat.cast_nonneg n) (hρ0 y))
  have hw1 (n : ℕ) (y : ℂ) : w n y ≤ 1 := min_le_left _ _
  have hG (n : ℕ) : Continuous (G n) := hF.mul (hw n)
  have hGcompact (n : ℕ) : HasCompactSupport (G n) := hFc.mul_right
  have hGsupport (n : ℕ) : Function.support (G n) ⊆ D := by
    intro y hy
    by_contra hyn
    have hz : ρ y = 0 := by
      have : y ∉ Function.support ρ := by rw [hρsupp]; exact hyn
      simpa only [Function.mem_support, not_not] using this
    apply hy
    simp [G, w, hz]
  have hGeq (n : ℕ) : ∫ y, G n y ∂μ = ∫ y, G n y ∂ν :=
    htest (G n) (hG n) (hGcompact n) (hGsupport n)
      (fun y => mul_nonneg (f y).coe_nonneg (hw0 n y))
  have hlim {y : ℂ} (hy : y ∈ D) : Tendsto (fun n => G n y) atTop (𝓝 (F y)) := by
    have hp := hρpos hy
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ρ y)
    have hevent : ∀ᶠ n : ℕ in atTop, G n y = F y := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hle : (1 : ℝ) ≤ (n : ℝ) * ρ y := by
        have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
        have hh : (1 : ℝ) / ρ y ≤ n := le_trans hN.le hn'
        exact (div_le_iff₀ hp).mp hh
      simp [G, w, min_eq_left hle]
    exact tendsto_const_nhds.congr' (hevent.mono fun _ h => h.symm)
  have hbound (n : ℕ) (y : ℂ) : ‖G n y‖ ≤ ‖F y‖ := by
    have hF0 : 0 ≤ F y := (f y).coe_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hF0 (hw0 n y)),
      Real.norm_eq_abs, abs_of_nonneg hF0]
    exact mul_le_of_le_one_right hF0 (hw1 n y)
  have haμ : ∀ᵐ y ∂μ, y ∈ D := by rw [ae_iff]; exact hμD
  have haν : ∀ᵐ y ∂ν, y ∈ D := by rw [ae_iff]; exact hνD
  have hintμ : Integrable (fun y => ‖F y‖) μ := (hF.integrable_of_hasCompactSupport hFc).norm
  have hintν : Integrable (fun y => ‖F y‖) ν := (hF.integrable_of_hasCompactSupport hFc).norm
  have hμ := tendsto_integral_of_dominated_convergence (fun y => ‖F y‖)
    (fun n => (hG n).stronglyMeasurable.aestronglyMeasurable) hintμ
    (fun n => Eventually.of_forall (hbound n)) (haμ.mono fun _ hy => hlim hy)
  have hν := tendsto_integral_of_dominated_convergence (fun y => ‖F y‖)
    (fun n => (hG n).stronglyMeasurable.aestronglyMeasurable) hintν
    (fun n => Eventually.of_forall (hbound n)) (haν.mono fun _ hy => hlim hy)
  exact tendsto_nhds_unique (hμ.congr (fun n => hGeq n)) hν

/-- The occupation measure of standard planar Brownian motion killed on leaving
a smooth bounded open set has density `2 * greenFunction D x` with respect to
planar Lebesgue measure. The starting point is any point of the set; no
connectivity assumption is required. -/
theorem occupationMeasure_eq_greenMeasure {D : Set ℂ} (hD : IsSmoothBoundedOpen D)
    {x : ℂ} (hx : x ∈ D) :
    occupationMeasure D (GreenGeneral.isOpen_of_isSmoothBoundedOpen hD) x = greenMeasure D x := by
  let hDo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  let : IsFiniteMeasure (occupationMeasure D hDo x) := isFiniteMeasure_occupationMeasure hDo hD.1 x
  let : IsFiniteMeasure (greenMeasure D x) := isFiniteMeasure_greenMeasure hDo hD.1 x
  exact measure_eq_of_nonneg_continuous_tests hDo _ _ (occupationMeasure_compl hDo x)
    (greenMeasure_compl hDo x) (fun f hf hfc hfs hf0 =>
      integral_occupationMeasure_eq_integral_greenMeasure_of_continuous hD hf hfc hfs hf0 hx)

/-- The killed occupation time of a Borel set is the integral of `2 G_D(x, y)`
over that set. -/
theorem occupationMeasure_apply {D : Set ℂ} (hD : IsSmoothBoundedOpen D)
    {x : ℂ} (hx : x ∈ D) {A : Set ℂ} (hA : MeasurableSet A) :
    occupationMeasure D (GreenGeneral.isOpen_of_isSmoothBoundedOpen hD) x A =
      ∫⁻ y in A, ENNReal.ofReal (2 * greenFunction D x y) := by
  rw [occupationMeasure_eq_greenMeasure hD hx, greenMeasure, withDensity_apply _ hA]

/-- For every Borel set, the expected time spent there by a planar Brownian
path before exiting the domain is the integral of the Green density. -/
theorem lintegral_brownian_occupation_eq_green {D : Set ℂ}
    (hD : IsSmoothBoundedOpen D) {x : ℂ} (hx : x ∈ D)
    {A : Set ℂ} (hA : MeasurableSet A) :
    (∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ),
        {t : ℝ | ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D p}.indicator
          (fun t => A.indicator (fun _ => (1 : ℝ≥0∞)) (p (Real.toNNReal t))) t)
        ∂(planarBrownianMotion x)) =
      ∫⁻ y in A, ENNReal.ofReal (2 * greenFunction D x y) := by
  have h := occupationMeasure_apply hD hx hA
  rw [← lintegral_indicator_one hA] at h
  change (∫⁻ y, A.indicator (fun _ => (1 : ℝ≥0∞)) y ∂occupationMeasure D
    (GreenGeneral.isOpen_of_isSmoothBoundedOpen hD) x) = _ at h
  rw [lintegral_occupationMeasure _ x (measurable_const.indicator hA)] at h
  exact h

/-- Every nonnegative Borel observable of the killed Brownian path has the
Green density `2 * G_D(x, ·)`. -/
theorem lintegral_brownian_occupation_eq_green_integral {D : Set ℂ}
    (hD : IsSmoothBoundedOpen D) {x : ℂ} (hx : x ∈ D)
    {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ),
        {t : ℝ | ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D p}.indicator
          (fun t => f (p (Real.toNNReal t))) t) ∂(planarBrownianMotion x)) =
      ∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) * f y := by
  let hDo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  have hmeas : AEMeasurable (fun y => ENNReal.ofReal (2 * greenFunction D x y)) volume :=
    ((integrable_greenFunction_pole hDo hD.1 x).const_mul 2).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  calc
    _ = ∫⁻ y, f y ∂occupationMeasure D hDo x := (lintegral_occupationMeasure hDo x hf).symm
    _ = ∫⁻ y, f y ∂greenMeasure D x := by rw [occupationMeasure_eq_greenMeasure hD hx]
    _ = _ := lintegral_withDensity_eq_lintegral_mul₀' hmeas hf.aemeasurable

/-- Any continuous off-diagonal representative of the killed occupation density
agrees pointwise with twice the Green kernel away from the starting point. -/
theorem occupation_density_eq_green_off_pole {D : Set ℂ} (hD : IsSmoothBoundedOpen D)
    {x : ℂ} (hx : x ∈ D) {k : ℂ → ℝ≥0∞} (hk : AEMeasurable k volume)
    (hkc : ContinuousOn k (D \ {x}))
    (hkocc : volume.withDensity k =
      occupationMeasure D (GreenGeneral.isOpen_of_isSmoothBoundedOpen hD) x) :
    Set.EqOn k (fun y => ENNReal.ofReal (2 * greenFunction D x y)) (D \ {x}) := by
  let hDo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  have hgm : AEMeasurable (fun y => ENNReal.ofReal (2 * greenFunction D x y)) volume :=
    ((integrable_greenFunction_pole hDo hD.1 x).const_mul 2).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have heq : volume.withDensity k = volume.withDensity
      (fun y => ENNReal.ofReal (2 * greenFunction D x y)) := by
    rw [hkocc, occupationMeasure_eq_greenMeasure hD hx, greenMeasure]
  have hae := (withDensity_eq_iff_of_sigmaFinite hk hgm).mp heq
  apply MeasureTheory.Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hae)
    (hDo.inter isClosed_singleton.isOpen_compl) hkc
  intro y hy
  have hxy : x ≠ y := by simpa using Ne.symm (show y ≠ x by simpa using hy.2)
  have hcont := continuousAt_greenFunction_uncurry hDo hD.1 hx hy.1 hxy
  exact (ENNReal.continuous_ofReal.continuousAt.comp
    ((continuousAt_const.mul (hcont.comp (continuousAt_const.prodMk continuousAt_id))))).continuousWithinAt


/-- A continuous occupation density can be integrated against any measure with
no atom at the pole, including measures singular to planar volume. Its potential
is twice the potential in the Laplacian normalization. -/
theorem occupation_density_potential_eq_green {D : Set ℂ} (hD : IsSmoothBoundedOpen D)
    {x : ℂ} (hx : x ∈ D) {k : ℂ → ℝ≥0∞} (hk : AEMeasurable k volume)
    (hkc : ContinuousOn k (D \ {x}))
    (hkocc : volume.withDensity k =
      occupationMeasure D (GreenGeneral.isOpen_of_isSmoothBoundedOpen hD) x)
    (μ : Measure ℂ) (hμ : μ {x} = 0) (f : ℂ → ℝ) :
    (IntegrableOn (fun y => (k y).toReal * f y) D μ ↔
      IntegrableOn (fun y => (2 * greenFunction D x y) * f y) D μ) ∧
    (∫ y in D, (k y).toReal * f y ∂μ) =
      2 * ∫ y in D, greenFunction D x y * f y ∂μ := by
  have heq := occupation_density_eq_green_off_pole hD hx hk hkc hkocc
  have hae : ∀ᵐ y ∂μ.restrict D, (k y).toReal * f y =
      (2 * greenFunction D x y) * f y := by
    filter_upwards [ae_restrict_mem (GreenGeneral.isOpen_of_isSmoothBoundedOpen hD).measurableSet,
      ae_restrict_of_ae (show ∀ᵐ y ∂μ, y ≠ x from compl_mem_ae_iff.2 hμ)] with y hy hyx
    rw [heq ⟨hy, by simpa using hyx⟩,
      ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (greenFunction_nonneg hD.1 x y))]
  constructor
  · exact integrable_congr hae
  · calc
      _ = ∫ y in D, (2 * greenFunction D x y) * f y ∂μ := integral_congr_ae hae
      _ = _ := by simp only [mul_assoc, integral_const_mul]


end HarmonicBalls.GreenOccupation
