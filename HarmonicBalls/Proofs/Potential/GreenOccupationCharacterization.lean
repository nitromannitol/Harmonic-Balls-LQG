import HarmonicBalls.Proofs.Potential.Fundamental
import HarmonicBalls.Proofs.Potential.GreenGeneralIdentification
import HarmonicBalls.Proofs.Sec6.BoundedHarmonicExit
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import HarmonicBalls.Proofs.Sec6.PlanarBrownianGenerator
import HarmonicBalls.Proofs.Sec6.StoppedPotentialIntegrability
import HarmonicBalls.Proofs.Sec3.ConservationOfMassStep3
import MarkovProcess.Trajectory.DynkinStopping
import MarkovProcess.Trajectory.ExpectedExitTime

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

end HarmonicBalls.GreenOccupation
