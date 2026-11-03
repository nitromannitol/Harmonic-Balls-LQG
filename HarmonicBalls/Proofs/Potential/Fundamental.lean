import HarmonicBalls.Defs.Green
import HarmonicBalls.Defs.Laplacian
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The fundamental solution of the Laplacian on the plane

The Newtonian (logarithmic) kernel `N(x,y) = -(2π)⁻¹ log |x - y|` (`newtonKernel`) is a fundamental solution of
`-Δ`: `ΔN(x,·) = -δ_x` in the sense of distributions (Proposition 2.3 of Bou-Rabee and Gwynne, *Harmonic balls in
Liouville quantum gravity*, line 480; Armitage–Gardiner, Theorem 4.3.? for the Riesz decomposition). That is, for
every test function `φ`,
`∫ N(x,y) Δφ(y) dy = -φ(x)` (`integral_newtonKernel_mul_laplacian`).

## Proof

* `log |·|` and `|·|⁻¹` are locally integrable on the plane (`integrableOn_ball_of_norm_le_rpow`).
* The regularized kernel `f_ε(y) = ½ log (|y - x|² + ε²)` is smooth, and two integrations by parts in the
  directions `1` and `i` give `∫ f_ε Δφ = -∫ Dφ(y)(y - x) / (|y - x|² + ε²) dy`.
* Letting `ε → 0` by dominated convergence, `∫ log |y - x| Δφ(y) dy = -∫ Dφ(y)(y - x) / |y - x|² dy`.
* In polar coordinates around `x`, `Dφ(x + r e^{iθ})(r e^{iθ}) / r² · r = ∂_r φ(x + r e^{iθ})`, so the last integral
  is `∫_{-π}^{π} ∫_0^∞ ∂_r φ(x + r e^{iθ}) dr dθ = -2π φ(x)`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Filter Topology Set Laplacian
open scoped ContDiff

/-! ## Local integrability of `log |·|` and `|·|⁻¹` -/

theorem abs_log_le_inv_add_self {s : ℝ} (hs : 0 < s) : |Real.log s| ≤ s⁻¹ + s := by
  rw [abs_le]
  constructor
  · have := Real.log_le_sub_one_of_pos (inv_pos.2 hs)
    rw [Real.log_inv] at this
    linarith
  · have := Real.log_le_sub_one_of_pos hs
    linarith [inv_pos.2 hs]

/-- `log |·|` is integrable on every disc `B_r(0)` of the plane. -/
theorem integrableOn_ball_log_norm (r : ℝ) :
    IntegrableOn (fun y : ℂ => Real.log ‖y‖) (ball 0 r) := by
  refine integrableOn_ball_of_norm_le_rpow (C := 1 + r ^ 2) (α := 1) (by simp) (by simp) ?_
    (Real.measurable_log.comp continuous_norm.measurable).aestronglyMeasurable
  refine ae_restrict_of_forall_mem measurableSet_ball fun y hy => ?_
  rw [mem_ball_zero_iff] at hy
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  have hs : 0 < ‖y‖ := norm_pos_iff.2 hy0
  rw [Real.norm_eq_abs, Real.rpow_neg_one]
  refine (abs_log_le_inv_add_self hs).trans ?_
  have h1 : ‖y‖ ≤ r ^ 2 * ‖y‖⁻¹ := by
    rw [le_mul_inv_iff₀ hs]
    nlinarith
  nlinarith

/-- `|·|⁻¹` is integrable on every disc `B_r(0)` of the plane. -/
theorem integrableOn_ball_inv_norm (r : ℝ) :
    IntegrableOn (fun y : ℂ => ‖y‖⁻¹) (ball 0 r) := by
  refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1) (by simp) (by simp) ?_ (by fun_prop)
  exact ae_of_all _ fun y => by simp [Real.rpow_neg_one]

/-- A function integrable on every disc `B_r(0)` and translated by `x` is locally integrable. -/
theorem locallyIntegrable_comp_sub_of_integrableOn_ball {f : ℂ → ℝ}
    (hf : ∀ r, IntegrableOn f (ball 0 r)) (x : ℂ) :
    LocallyIntegrable (fun y => f (y - x)) := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball x
  have h := (measurePreserving_sub_right volume x).integrableOn_comp_preimage
    (measurableEmbedding_subRight x) |>.2 (hf r)
  refine h.mono_set fun y hy => ?_
  simpa [mem_preimage, mem_ball, dist_eq_norm] using hr hy

/-- The Newtonian kernel `N(x,·)` is locally integrable on the plane. -/
theorem locallyIntegrable_newtonKernel (x : ℂ) : LocallyIntegrable (newtonKernel x) := by
  have h := (locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm x).smul
    (-(2 * Real.pi)⁻¹)
  convert h using 1
  funext y
  simp [newtonKernel, norm_sub_rev]

/-- `|· - x|⁻¹` is locally integrable on the plane. -/
theorem locallyIntegrable_inv_norm_sub (x : ℂ) : LocallyIntegrable (fun y : ℂ => ‖y - x‖⁻¹) :=
  locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_inv_norm x

/-! ## The radial derivative in polar coordinates -/

/-- The unit vector `e^{iθ}` in polar coordinates. -/
theorem polarCoord_symm_eq_mul (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = r * Complex.polarCoord.symm (1, θ) := by
  simp [Complex.polarCoord_symm_apply]

theorem norm_polarCoord_symm_one (θ : ℝ) : ‖Complex.polarCoord.symm (1, θ)‖ = 1 := by
  simp

/-- A compactly supported `C¹` function and its derivative vanish beyond the radius `M` of a disc around `x`
containing the support. -/
theorem exists_radius_fderiv_eq_zero {φ : ℂ → ℝ} (hc : HasCompactSupport φ) (x : ℂ) :
    ∃ M, 0 ≤ M ∧ ∀ y, M < ‖y - x‖ → φ y = 0 ∧ fderiv ℝ φ y = 0 := by
  obtain ⟨M, hM⟩ := hc.isCompact.isBounded.subset_closedBall x
  refine ⟨max M 0, le_max_right _ _, fun y hy => ?_⟩
  have hy' : y ∉ tsupport φ := fun h => by
    have := hM h
    rw [mem_closedBall, dist_eq_norm] at this
    linarith [le_max_left M 0]
  exact ⟨image_eq_zero_of_notMem_tsupport hy',
    image_eq_zero_of_notMem_tsupport fun h => hy' (tsupport_fderiv_subset ℝ h)⟩

/-- **The radial integral.** For a compactly supported `C¹` function `φ` on the plane,
`∫ Dφ(y)(y - x) / |y - x|² dy = -2π φ(x)`: in polar coordinates around `x` the integrand times the Jacobian `r` is
the radial derivative `∂_r φ(x + r e^{iθ})`. -/
theorem integral_fderiv_div_norm_sq {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (x : ℂ) :
    ∫ y, fderiv ℝ φ y (y - x) / ‖y - x‖ ^ 2 = -(2 * Real.pi) * φ x := by
  set e : ℝ → ℂ := fun θ => Complex.polarCoord.symm (1, θ) with he
  set g : ℝ × ℝ → ℝ := fun p => fderiv ℝ φ (x + p.1 * e p.2) (e p.2) with hg
  have he1 : ∀ θ, ‖e θ‖ = 1 := fun θ => by simp [he]
  have hpolar : ∀ r θ : ℝ, Complex.polarCoord.symm (r, θ) = r * e θ := fun r θ => by
    simp [he, Complex.polarCoord_symm_apply]
  have hcont' : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have he_cont : Continuous e := by
    simp only [he, Complex.polarCoord_symm_apply]; fun_prop
  have hg_cont : Continuous g := by
    simp only [hg]
    exact (hcont'.comp (by fun_prop)).clm_apply (he_cont.comp continuous_snd)
  obtain ⟨M, hM0, hM⟩ := exists_radius_fderiv_eq_zero hc x
  have hgM : ∀ p : ℝ × ℝ, 0 ≤ p.1 → M < p.1 → g p = 0 := by
    intro p hp hMp
    have : M < ‖x + p.1 * e p.2 - x‖ := by
      simp [he, abs_of_nonneg hp, hMp]
    simp [hg, (hM _ this).2]
  -- Step 1: translate and pass to polar coordinates.
  have h1 : ∫ y, fderiv ℝ φ y (y - x) / ‖y - x‖ ^ 2 =
      ∫ p in Complex.polarCoord.target, g p := by
    have := integral_sub_right_eq_self (μ := volume)
      (fun u : ℂ => fderiv ℝ φ (u + x) u / ‖u‖ ^ 2) x
    simp only [sub_add_cancel] at this
    rw [this, ← Complex.integral_comp_polarCoord_symm]
    refine setIntegral_congr_fun Complex.polarCoord.open_target.measurableSet fun p hp => ?_
    have hp1 : 0 < p.1 := hp.1
    obtain ⟨r, θ⟩ := p
    simp only at hp1 ⊢
    rw [hpolar, norm_mul, he1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp1, mul_one,
      ← Complex.real_smul, ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul, add_comm]
    simp only [hg, ← Complex.real_smul]
    field_simp
  -- Step 2: Fubini, with the angle outside.
  have htarget : Complex.polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := rfl
  have hint : IntegrableOn g (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
    have hK : IntegrableOn g (Icc 0 M ×ˢ Icc (-Real.pi) Real.pi) :=
      hg_cont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    refine hK.of_forall_sdiff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    rintro p ⟨⟨hp1, hp2⟩, hpn⟩
    refine hgM p (le_of_lt hp1) ?_
    by_contra h
    push Not at h
    exact hpn ⟨⟨le_of_lt hp1, h⟩, ⟨hp2.1.le, hp2.2.le⟩⟩
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hint
  rw [h1, htarget, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm g hint]
  -- Step 3: the radial integral of the radial derivative.
  have h2 : ∀ θ, ∫ r in Ioi (0 : ℝ), g (r, θ) = -φ x := by
    intro θ
    have hderiv : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt (fun r : ℝ => φ (x + r * e θ)) (g (r, θ)) r := by
      intro r _
      have h := ((hφ.differentiable one_ne_zero) (x + r * e θ)).hasFDerivAt.comp_hasDerivAt r
        (((hasDerivAt_id r).ofReal_comp.mul_const (e θ)).const_add x)
      simp only [id, Complex.ofReal_one, one_mul] at h
      exact h
    have hintθ : IntegrableOn (fun r => g (r, θ)) (Ioi 0) := by
      have hK : IntegrableOn (fun r => g (r, θ)) (Icc 0 M) :=
        (hg_cont.comp (by fun_prop : Continuous fun r : ℝ => (r, θ))).continuousOn.integrableOn_compact
          isCompact_Icc
      refine hK.of_forall_sdiff_eq_zero measurableSet_Ioi ?_
      rintro r ⟨hr, hrn⟩
      refine hgM (r, θ) (le_of_lt hr) ?_
      by_contra h
      push Not at h
      exact hrn ⟨le_of_lt hr, h⟩
    have hlim : Tendsto (fun r : ℝ => φ (x + r * e θ)) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop M] with r hr
      have : M < ‖x + r * e θ - x‖ := by simp [he1, abs_of_pos (hM0.trans_lt hr), hr]
      exact ((hM _ this).1).symm
    have hcont0 : ContinuousWithinAt (fun r : ℝ => φ (x + r * e θ)) (Ici 0) 0 :=
      (hφ.continuous.comp (by fun_prop)).continuousWithinAt
    rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont0 hderiv hintθ hlim]
    simp
  simp only [h2, setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo]
  rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

/-! ## The Laplacian as a sum of second directional derivatives -/

/-- On the plane, `Δφ = ∂₁∂₁φ + ∂ᵢ∂ᵢφ`, written with iterated directional (Fréchet) derivatives. -/
theorem laplacian_eq_fderiv_fderiv {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (y : ℂ) :
    Δ φ y = fderiv ℝ (fun z => fderiv ℝ φ z 1) y 1 +
      fderiv ℝ (fun z => fderiv ℝ φ z Complex.I) y Complex.I := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) y :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) y
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-! ## The regularized logarithmic kernel -/

/-- The regularized logarithm `f_ε(y) = ½ log (|y - x|² + ε²)`, a smooth approximation of `log |y - x|`. -/
noncomputable def regLog (x : ℂ) (ε : ℝ) (y : ℂ) : ℝ :=
  (1 / 2) * Real.log (‖y - x‖ ^ 2 + ε ^ 2)

theorem regLog_arg_pos (x : ℂ) {ε : ℝ} (hε : 0 < ε) (y : ℂ) : 0 < ‖y - x‖ ^ 2 + ε ^ 2 := by
  positivity

theorem hasFDerivAt_regLog (x : ℂ) {ε : ℝ} (hε : 0 < ε) (y : ℂ) :
    HasFDerivAt (regLog x ε)
      ((1 / 2 : ℝ) • (‖y - x‖ ^ 2 + ε ^ 2)⁻¹ • (2 • (innerSL ℝ (y - x)).comp
        (ContinuousLinearMap.id ℝ ℂ))) y := by
  have h1 : HasFDerivAt (fun y : ℂ => y - x) (ContinuousLinearMap.id ℝ ℂ) y :=
    (hasFDerivAt_id y).sub_const x
  exact (((h1.norm_sq).add_const (ε ^ 2)).log (regLog_arg_pos x hε y).ne').const_mul (1 / 2)

theorem fderiv_regLog_apply (x : ℂ) {ε : ℝ} (hε : 0 < ε) (y v : ℂ) :
    fderiv ℝ (regLog x ε) y v = inner ℝ (y - x) v / (‖y - x‖ ^ 2 + ε ^ 2) := by
  rw [(hasFDerivAt_regLog x hε y).fderiv]
  simp
  field_simp
  ring

theorem continuous_regLog (x : ℂ) {ε : ℝ} (hε : 0 < ε) : Continuous (regLog x ε) :=
  continuous_iff_continuousAt.2 fun y => (hasFDerivAt_regLog x hε y).continuousAt

theorem continuous_fderiv_regLog_apply (x : ℂ) {ε : ℝ} (hε : 0 < ε) (v : ℂ) :
    Continuous fun y => fderiv ℝ (regLog x ε) y v := by
  simp_rw [fderiv_regLog_apply x hε]
  exact Continuous.div (by fun_prop) (by fun_prop) fun y => (regLog_arg_pos x hε y).ne'

/-- **Integration by parts against the regularized kernel.**
`∫ f_ε Δφ = -∫ Dφ(y)(y - x) / (|y - x|² + ε²) dy`. -/
theorem integral_regLog_mul_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (x : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∫ y, regLog x ε y * Δ φ y = -∫ y, fderiv ℝ φ y (y - x) / (‖y - x‖ ^ 2 + ε ^ 2) := by
  have hφ1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
  -- the one-direction identity
  have key : ∀ v : ℂ, Integrable (fun y => fderiv ℝ (regLog x ε) y v * fderiv ℝ φ y v) ∧
      Integrable (fun y => regLog x ε y * fderiv ℝ (fun z => fderiv ℝ φ z v) y v) ∧
      ∫ y, regLog x ε y * fderiv ℝ (fun z => fderiv ℝ φ z v) y v =
        -∫ y, fderiv ℝ (regLog x ε) y v * fderiv ℝ φ y v := by
    intro v
    have hgv : ContDiff ℝ 1 (fun z => fderiv ℝ φ z v) := hφ1.clm_apply contDiff_const
    have hgc : HasCompactSupport (fun z => fderiv ℝ φ z v) :=
      (hc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v) (by simp)
    have hg'c : HasCompactSupport (fun z => fderiv ℝ (fun z => fderiv ℝ φ z v) z v) :=
      (hgc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v) (by simp)
    have hg'cont : Continuous (fun z => fderiv ℝ (fun z => fderiv ℝ φ z v) z v) :=
      (hgv.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have i1 : Integrable (fun y => fderiv ℝ (regLog x ε) y v * fderiv ℝ φ y v) :=
      ((continuous_fderiv_regLog_apply x hε v).mul hgv.continuous).integrable_of_hasCompactSupport
        hgc.mul_left
    have i2 : Integrable (fun y => regLog x ε y * fderiv ℝ (fun z => fderiv ℝ φ z v) y v) :=
      ((continuous_regLog x hε).mul hg'cont).integrable_of_hasCompactSupport hg'c.mul_left
    have i3 : Integrable (fun y => regLog x ε y * fderiv ℝ φ y v) :=
      ((continuous_regLog x hε).mul hgv.continuous).integrable_of_hasCompactSupport hgc.mul_left
    exact ⟨i1, i2, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i1 i2 i3
      (fun y _ => (hasFDerivAt_regLog x hε y).differentiableAt)
      (fun y _ => (hgv.differentiable one_ne_zero) y)⟩
  obtain ⟨a1, b1, c1⟩ := key 1
  obtain ⟨a2, b2, c2⟩ := key Complex.I
  simp_rw [laplacian_eq_fderiv_fderiv hφ, mul_add]
  rw [integral_add b1 b2, c1, c2, ← neg_add, ← integral_add a1 a2]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [fderiv_regLog_apply x hε]
  have hy : y - x = ((y - x).re : ℝ) • (1 : ℂ) + ((y - x).im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  have hD : fderiv ℝ φ y (y - x) =
      (y - x).re * fderiv ℝ φ y 1 + (y - x).im * fderiv ℝ φ y Complex.I := by
    conv_lhs => rw [hy]
    simp only [map_add, map_smul, smul_eq_mul]
  have h1 : inner ℝ (y - x) (1 : ℂ) = (y - x).re := by simp [Complex.inner]
  have hI : inner ℝ (y - x) Complex.I = (y - x).im := by simp [Complex.inner]; ring
  rw [h1, hI, hD]
  field_simp

/-! ## Letting `ε → 0` -/

theorem continuous_laplacian_of_contDiff {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) : Continuous (Δ φ) := by
  have hφ1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
  have h : ∀ v : ℂ, Continuous fun y => fderiv ℝ (fun z => fderiv ℝ φ z v) y v := fun v =>
    ((hφ1.clm_apply contDiff_const).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have he : Δ φ = fun y => fderiv ℝ (fun z => fderiv ℝ φ z 1) y 1 +
      fderiv ℝ (fun z => fderiv ℝ φ z Complex.I) y Complex.I := funext (laplacian_eq_fderiv_fderiv hφ)
  rw [he]
  exact (h 1).add (h Complex.I)

theorem support_laplacian_subset (φ : ℂ → ℝ) : Function.support (Δ φ) ⊆ tsupport φ := by
  intro y hy
  by_contra hy'
  apply hy
  have h0 : φ =ᶠ[𝓝 y] (0 : ℂ → ℝ) := notMem_tsupport_iff_eventuallyEq.1 hy'
  rw [(InnerProductSpace.laplacian_congr_nhds h0).eq_of_nhds,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp

/-- The Laplacian does not enlarge supports: `tsupport (Δφ) ⊆ tsupport φ`. -/
theorem tsupport_laplacian_subset (φ : ℂ → ℝ) : tsupport (Δ φ) ⊆ tsupport φ :=
  closure_minimal (support_laplacian_subset φ) (isClosed_tsupport φ)

theorem hasCompactSupport_laplacian {φ : ℂ → ℝ} (hc : HasCompactSupport φ) : HasCompactSupport (Δ φ) :=
  hc.mono' (support_laplacian_subset φ)

theorem abs_half_log_le {r ε : ℝ} (hr : 0 < r) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    |1 / 2 * Real.log (r ^ 2 + ε ^ 2)| ≤ |Real.log r| + Real.log (r ^ 2 + 1) := by
  have hs : 0 < r ^ 2 + ε ^ 2 := by positivity
  have hl1 : 0 ≤ Real.log (r ^ 2 + 1) := Real.log_nonneg (by nlinarith)
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  rcases le_or_gt 1 (r ^ 2 + ε ^ 2) with h | h
  · have h0 := Real.log_nonneg h
    have h2 := Real.log_le_log hs (by linarith : r ^ 2 + ε ^ 2 ≤ r ^ 2 + 1)
    rw [abs_of_nonneg (by positivity)]
    linarith [abs_nonneg (Real.log r)]
  · have hneg : Real.log (r ^ 2 + ε ^ 2) < 0 := Real.log_neg hs h
    have hle : Real.log (r ^ 2) ≤ Real.log (r ^ 2 + ε ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have hp : Real.log (r ^ 2) = 2 * Real.log r := by rw [Real.log_pow]; norm_num
    rw [abs_of_neg (by linarith)]
    linarith [neg_le_abs (Real.log r)]

theorem ae_ne_complex (x : ℂ) : ∀ᵐ y : ℂ, y ≠ x := by
  rw [ae_iff]
  simp

/-- `∫ f_ε Δφ → ∫ log |y - x| Δφ(y) dy` as `ε → 0⁺`. -/
theorem tendsto_integral_regLog_mul_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (x : ℂ) :
    Tendsto (fun ε => ∫ y, regLog x ε y * Δ φ y) (𝓝[>] 0)
      (𝓝 (∫ y, Real.log ‖y - x‖ * Δ φ y)) := by
  have hΔ := continuous_laplacian_of_contDiff hφ
  have hΔc := hasCompactSupport_laplacian hc
  have hlog0 : LocallyIntegrable (fun y => Real.log ‖y - x‖) :=
    locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm x
  have hlog : LocallyIntegrable (fun y => |Real.log ‖y - x‖|) := by
    refine LocallyIntegrable.mono hlog0 ((Real.measurable_log.comp
      (continuous_norm.comp (continuous_id.sub continuous_const)).measurable).abs).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    simp
  refine tendsto_integral_filter_of_dominated_convergence
    (fun y => |Δ φ y| * |Real.log ‖y - x‖| + |Δ φ y| * Real.log (‖y - x‖ ^ 2 + 1)) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ((continuous_regLog x hε).mul hΔ).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    filter_upwards [ae_ne_complex x] with y hy
    have hr : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
    rw [Real.norm_eq_abs, abs_mul, regLog, mul_comm]
    have := abs_half_log_le hr hε.1 hε.2
    have h0 := abs_nonneg (Δ φ y)
    nlinarith
  · refine Integrable.add ?_ ?_
    · exact hlog.integrable_smul_left_of_hasCompactSupport hΔ.abs hΔc.abs
    · exact (hΔ.abs.mul (Continuous.log (by fun_prop) fun y => by positivity)).integrable_of_hasCompactSupport
        hΔc.abs.mul_right
  · filter_upwards [ae_ne_complex x] with y hy
    have hr : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
    have h1 : Tendsto (fun ε : ℝ => ‖y - x‖ ^ 2 + ε ^ 2) (𝓝 0) (𝓝 (‖y - x‖ ^ 2 + 0 ^ 2)) :=
      (continuous_const.add (continuous_pow 2)).tendsto 0
    have h2 := ((h1.log (by positivity)).const_mul (1 / 2)).mul_const (Δ φ y)
    have h3 : 1 / 2 * Real.log (‖y - x‖ ^ 2 + 0 ^ 2) = Real.log ‖y - x‖ := by
      rw [zero_pow two_ne_zero, add_zero, Real.log_pow]; push_cast; ring
    rw [h3] at h2
    exact h2.mono_left nhdsWithin_le_nhds

/-- `∫ Dφ(y)(y - x) / (|y - x|² + ε²) dy → ∫ Dφ(y)(y - x) / |y - x|² dy` as `ε → 0⁺`. -/
theorem tendsto_integral_fderiv_div {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (x : ℂ) :
    Tendsto (fun ε => ∫ y, fderiv ℝ φ y (y - x) / (‖y - x‖ ^ 2 + ε ^ 2)) (𝓝[>] 0)
      (𝓝 (∫ y, fderiv ℝ φ y (y - x) / ‖y - x‖ ^ 2)) := by
  have hD : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv two_ne_zero
  have hDc : HasCompactSupport (fun y => ‖fderiv ℝ φ y‖) := (hc.fderiv ℝ).norm
  refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖fderiv ℝ φ y‖ * ‖y - x‖⁻¹)
    ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine (Continuous.div (hD.clm_apply (by fun_prop)) (by fun_prop) fun y => ?_).aestronglyMeasurable
    exact (regLog_arg_pos x hε y).ne'
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine ae_of_all _ fun y => ?_
    rcases eq_or_ne y x with rfl | hy
    · simp
    have hr : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
    have hs := regLog_arg_pos x hε y
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hs]
    have h1 : |fderiv ℝ φ y (y - x)| ≤ ‖fderiv ℝ φ y‖ * ‖y - x‖ := by
      simpa [Real.norm_eq_abs] using (fderiv ℝ φ y).le_opNorm (y - x)
    have h2 : ‖fderiv ℝ φ y‖ * ‖y - x‖⁻¹ = ‖fderiv ℝ φ y‖ * ‖y - x‖ / ‖y - x‖ ^ 2 := by
      field_simp
    rw [h2, div_le_div_iff₀ hs (by positivity)]
    have h3 : ‖y - x‖ ^ 2 ≤ ‖y - x‖ ^ 2 + ε ^ 2 := by nlinarith
    have h4 : 0 ≤ ‖fderiv ℝ φ y‖ * ‖y - x‖ := by positivity
    calc |fderiv ℝ φ y (y - x)| * ‖y - x‖ ^ 2 ≤ ‖fderiv ℝ φ y‖ * ‖y - x‖ * ‖y - x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ ‖fderiv ℝ φ y‖ * ‖y - x‖ * (‖y - x‖ ^ 2 + ε ^ 2) := mul_le_mul_of_nonneg_left h3 h4
  · exact (locallyIntegrable_inv_norm_sub x).integrable_smul_left_of_hasCompactSupport hD.norm hDc
  · filter_upwards [ae_ne_complex x] with y hy
    have hr : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
    have h1 : Tendsto (fun ε : ℝ => ‖y - x‖ ^ 2 + ε ^ 2) (𝓝 0) (𝓝 (‖y - x‖ ^ 2 + 0 ^ 2)) :=
      (continuous_const.add (continuous_pow 2)).tendsto 0
    rw [zero_pow two_ne_zero, add_zero] at h1
    exact (tendsto_const_nhds.div h1 (by positivity)).mono_left nhdsWithin_le_nhds

/-- `∫ log |y - x| Δφ(y) dy = 2π φ(x)` for a compactly supported `C²` function `φ`. -/
theorem integral_log_norm_sub_mul_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (x : ℂ) :
    ∫ y, Real.log ‖y - x‖ * Δ φ y = 2 * Real.pi * φ x := by
  have hA := tendsto_integral_regLog_mul_laplacian hφ hc x
  have hB := (tendsto_integral_fderiv_div hφ hc x).neg
  rw [integral_fderiv_div_norm_sq (hφ.of_le (by norm_num)) hc x] at hB
  have hAB : (fun ε => ∫ y, regLog x ε y * Δ φ y) =ᶠ[𝓝[>] 0]
      fun ε => -∫ y, fderiv ℝ φ y (y - x) / (‖y - x‖ ^ 2 + ε ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact integral_regLog_mul_laplacian hφ hc x hε
  rw [tendsto_nhds_unique (hA.congr' hAB) hB]
  ring

/-- **The Newtonian kernel is a fundamental solution of `-Δ`.** For every compactly supported `C²` function `φ` on
the plane and every `x`, `∫ N(x,y) Δφ(y) dy = -φ(x)`, i.e. `ΔN(x,·) = -δ_x` in the sense of distributions
(Proposition 2.3, line 482, for the whole plane). -/
theorem integral_newtonKernel_mul_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (x : ℂ) :
    ∫ y, newtonKernel x y * Δ φ y = -φ x := by
  have h : ∀ y, newtonKernel x y * Δ φ y = -(2 * Real.pi)⁻¹ * (Real.log ‖y - x‖ * Δ φ y) := by
    intro y; rw [newtonKernel, norm_sub_rev]; ring
  simp_rw [h]
  rw [integral_const_mul, integral_log_norm_sub_mul_laplacian hφ hc x]
  field_simp

/-- `Δφ` has integral zero for a compactly supported `C²` function `φ`. -/
theorem integral_laplacian_eq_zero {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    ∫ y, Δ φ y = 0 := by
  have hφ1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
  have key : ∀ v : ℂ, ∫ y, fderiv ℝ (fun z => fderiv ℝ φ z v) y v = 0 := by
    intro v
    have hgv : ContDiff ℝ 1 (fun z => fderiv ℝ φ z v) := hφ1.clm_apply contDiff_const
    have hgc : HasCompactSupport (fun z => fderiv ℝ φ z v) :=
      (hc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v) (by simp)
    have hg'c : HasCompactSupport (fun z => fderiv ℝ (fun z => fderiv ℝ φ z v) z v) :=
      (hgc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v) (by simp)
    have hg'cont : Continuous (fun z => fderiv ℝ (fun z => fderiv ℝ φ z v) z v) :=
      (hgv.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := fun _ : ℂ => (1 : ℝ))
      (g := fun z => fderiv ℝ φ z v) (v := v) (μ := volume) (by simp)
      (by simpa using hg'cont.integrable_of_hasCompactSupport hg'c)
      (by simpa using hgv.continuous.integrable_of_hasCompactSupport hgc)
      (fun _ _ => differentiableAt_const _) (fun y _ => (hgv.differentiable one_ne_zero) y)
    simpa using h
  simp_rw [laplacian_eq_fderiv_fderiv hφ]
  have hint : ∀ v : ℂ, Integrable fun y => fderiv ℝ (fun z => fderiv ℝ φ z v) y v := by
    intro v
    have hgc : HasCompactSupport (fun z => fderiv ℝ φ z v) :=
      (hc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v) (by simp)
    exact (((hφ1.clm_apply contDiff_const).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport
      ((hgc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v) (by simp))
  rw [integral_add (hint 1) (hint Complex.I), key, key, add_zero]

end HarmonicBalls
