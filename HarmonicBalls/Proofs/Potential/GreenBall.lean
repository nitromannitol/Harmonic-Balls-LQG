import HarmonicBalls.Defs.Green

/-!
# The Green function of a disc

Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795), Section 2.2
(subsec:green, lines 466-489; Proposition 2.3, prop:green-properties, line 480).

For `R > 0` and `x, y ∈ B_R(0)`, `x ≠ y`, the Green function `G_{B_R}` of `Defs/Green.lean` (the Newtonian kernel
minus its greatest harmonic minorant, Armitage–Gardiner §4.1) is given by the explicit formula
`G_{B_R}(x,y) = (2π)⁻¹ log (|R² - x̄ y| / (R |x - y|))` (`greenFunction_ball`).

## Proof

Write `N(x,y) = -(2π)⁻¹ log |x - y|` and `h_x(y) = -(2π)⁻¹ log (|R² - x̄ y| / R)`
(`greatestHarmonicMinorantBall`), so that `N(x,·) - h_x = greenBall R x` off the pole. The function `h_x` is
harmonic on a neighbourhood of `closedBall 0 R` (it is `log` of the modulus of a non-vanishing affine function). The
algebraic identity `|R² - x̄ y|² = R² |x - y|² + (R² - |x|²)(R² - |y|²)` gives `greenBall R x ≥ 0` on the disc, so
`h_x` is a harmonic minorant of `N(x,·)`. Conversely, if `h` is any harmonic minorant, then `h - h_x` is harmonic on
`B_R(0)` and bounded above by `greenBall R x`, which is at most
`(R² - |x|²)(R² - ρ²) / (4π R² (ρ - |x|)²)` on the circle `|y| = ρ`. The maximum principle on `closedBall 0 ρ`
(`le_of_forall_mem_sphere_le_of_harmonicOnNhd`, deduced from the maximum modulus principle for `exp ∘ F`, where
`h - h_x = Re F` with `F` holomorphic) and `ρ → R⁻` give `h ≤ h_x`. Hence `h_x` is the greatest harmonic minorant
(`greatestHarmonicMinorant_ball`).

## Main statements

* `greenFunction_ball`: `G_{B_R}(x,y) = greenBall R x y` for `x, y ∈ B_R(0)`, `x ≠ y`;
* `greenFunction_ball_comm`: symmetry `G_{B_R}(x,y) = G_{B_R}(y,x)`;
* `greenFunction_ball_pos`: `G_{B_R}(x,y) > 0` for `x, y ∈ B_R(0)`, `x ≠ y` (Proposition 2.3, "Positive");
* `greenFunction_ball_of_le_norm`, `continuousOn_greenFunction_ball`: `G_{B_R}(x,·)` vanishes off `B_R(0)` and is
  continuous on `ℂ \ {x}`, so it has boundary values `0` on `∂B_R(0)` (Proposition 2.3, "Zero boundary");
* `harmonicOnNhd_greenFunction_ball`, `contDiffOn_greenFunction_ball`: `G_{B_R}(x,·)` is harmonic, hence
  infinitely differentiable (indeed real analytic), on `B_R(0) \ {x}` (Proposition 2.3, "Smooth away from the
  pole").
-/

namespace HarmonicBalls

open Metric Filter Topology InnerProductSpace ComplexConjugate

/-! ## The algebraic identity -/

/-- `|R² - x̄ y|² = R² |x - y|² + (R² - |x|²)(R² - |y|²)`. -/
theorem norm_sq_sub_conj_mul (R : ℝ) (x y : ℂ) :
    ‖(R : ℂ) ^ 2 - conj x * y‖ ^ 2 =
      R ^ 2 * ‖x - y‖ ^ 2 + (R ^ 2 - ‖x‖ ^ 2) * (R ^ 2 - ‖y‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, ← Complex.ofReal_pow, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- For `|x| < R` and `|y| ≤ R`, `R² - x̄ y ≠ 0`. -/
theorem norm_sub_conj_mul_pos {R : ℝ} (hR : 0 < R) {x y : ℂ} (hx : ‖x‖ < R) (hy : ‖y‖ ≤ R) :
    0 < ‖(R : ℂ) ^ 2 - conj x * y‖ := by
  have h1 : ‖conj x * y‖ < R ^ 2 := by
    rw [norm_mul, Complex.norm_conj, sq]
    calc ‖x‖ * ‖y‖ ≤ ‖x‖ * R := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
      _ < R * R := mul_lt_mul_of_pos_right hx hR
  have h2 : ‖(R : ℂ) ^ 2‖ = R ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have h3 := norm_sub_norm_le ((R : ℂ) ^ 2) (conj x * y)
  linarith

/-! ## Sign and size of `greenBall` -/

/-- `greenBall R x y ≥ 0` for `x, y ∈ closedBall 0 R`. -/
theorem greenBall_nonneg {R : ℝ} (hR : 0 < R) {x y : ℂ} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    0 ≤ greenBall R x y := by
  rcases eq_or_ne x y with rfl | hxy
  · rw [greenBall_self]
  have hb : 0 < R * ‖x - y‖ := mul_pos hR (norm_pos_iff.2 (sub_ne_zero.2 hxy))
  have hid := norm_sq_sub_conj_mul R x y
  have h1 : 0 ≤ (R ^ 2 - ‖x‖ ^ 2) * (R ^ 2 - ‖y‖ ^ 2) :=
    mul_nonneg (by nlinarith [norm_nonneg x]) (by nlinarith [norm_nonneg y])
  have hle : R * ‖x - y‖ ≤ ‖(R : ℂ) ^ 2 - conj x * y‖ := by
    nlinarith [norm_nonneg ((R : ℂ) ^ 2 - conj x * y)]
  exact mul_nonneg (by positivity) (Real.log_nonneg ((one_le_div hb).2 hle))

/-- `greenBall R x y > 0` for `x, y ∈ B_R(0)`, `x ≠ y`. -/
theorem greenBall_pos {R : ℝ} (hR : 0 < R) {x y : ℂ} (hx : ‖x‖ < R) (hy : ‖y‖ < R) (hxy : x ≠ y) :
    0 < greenBall R x y := by
  have hb : 0 < R * ‖x - y‖ := mul_pos hR (norm_pos_iff.2 (sub_ne_zero.2 hxy))
  have hid := norm_sq_sub_conj_mul R x y
  have h1 : 0 < (R ^ 2 - ‖x‖ ^ 2) * (R ^ 2 - ‖y‖ ^ 2) :=
    mul_pos (by nlinarith [norm_nonneg x]) (by nlinarith [norm_nonneg y])
  have hlt : R * ‖x - y‖ < ‖(R : ℂ) ^ 2 - conj x * y‖ := by
    nlinarith [norm_nonneg ((R : ℂ) ^ 2 - conj x * y)]
  exact mul_pos (by positivity) (Real.log_pos ((one_lt_div hb).2 hlt))

/-- `greenBall R x y ≤ 0` for `|x| ≤ R ≤ |y|`. -/
theorem greenBall_nonpos {R : ℝ} (hR : 0 < R) {x y : ℂ} (hx : ‖x‖ ≤ R) (hy : R ≤ ‖y‖) :
    greenBall R x y ≤ 0 := by
  rcases eq_or_ne x y with rfl | hxy
  · rw [greenBall_self]
  have hb : 0 < R * ‖x - y‖ := mul_pos hR (norm_pos_iff.2 (sub_ne_zero.2 hxy))
  have hid := norm_sq_sub_conj_mul R x y
  have h1 : (R ^ 2 - ‖x‖ ^ 2) * (R ^ 2 - ‖y‖ ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith [norm_nonneg x]) (by nlinarith [norm_nonneg y])
  have hle : ‖(R : ℂ) ^ 2 - conj x * y‖ ≤ R * ‖x - y‖ := by
    nlinarith [norm_nonneg ((R : ℂ) ^ 2 - conj x * y)]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (Real.log_nonpos (by positivity) ((div_le_one hb).2 hle))

/-- `greenBall R x z ≤ (4π)⁻¹ (R² - |x|²)(R² - |z|²) / (R² |x - z|²)` (from `log t ≤ t - 1`). -/
theorem greenBall_le {R : ℝ} (hR : 0 < R) {x z : ℂ} (hxz : x ≠ z)
    (ha : 0 < ‖(R : ℂ) ^ 2 - conj x * z‖) :
    greenBall R x z ≤
      (4 * Real.pi)⁻¹ * ((R ^ 2 - ‖x‖ ^ 2) * (R ^ 2 - ‖z‖ ^ 2) / (R ^ 2 * ‖x - z‖ ^ 2)) := by
  have hn : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hxz)
  have hb : 0 < R * ‖x - z‖ := mul_pos hR hn
  have hid := norm_sq_sub_conj_mul R x z
  have hlog : Real.log ((‖(R : ℂ) ^ 2 - conj x * z‖ / (R * ‖x - z‖)) ^ 2) ≤
      (‖(R : ℂ) ^ 2 - conj x * z‖ / (R * ‖x - z‖)) ^ 2 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have heq : (‖(R : ℂ) ^ 2 - conj x * z‖ / (R * ‖x - z‖)) ^ 2 - 1 =
      (R ^ 2 - ‖x‖ ^ 2) * (R ^ 2 - ‖z‖ ^ 2) / (R ^ 2 * ‖x - z‖ ^ 2) := by
    rw [div_pow, mul_pow, hid]
    field_simp
    ring
  rw [Real.log_pow, heq] at hlog
  have hπ : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  calc greenBall R x z = (2 * Real.pi)⁻¹ * Real.log (‖(R : ℂ) ^ 2 - conj x * z‖ / (R * ‖x - z‖)) := rfl
    _ ≤ (2 * Real.pi)⁻¹ * ((R ^ 2 - ‖x‖ ^ 2) * (R ^ 2 - ‖z‖ ^ 2) / (R ^ 2 * ‖x - z‖ ^ 2) / 2) := by
      apply mul_le_mul_of_nonneg_left _ hπ
      push_cast at hlog
      linarith
    _ = _ := by ring

/-- On the circle `|z| = ρ` with `|x| < ρ ≤ R`:
`greenBall R x z ≤ (4π)⁻¹ (R² - |x|²)(R² - ρ²) / (R² (ρ - |x|)²)`. -/
theorem greenBall_le_of_norm_eq {R ρ : ℝ} (hR : 0 < R) {x z : ℂ} (hxρ : ‖x‖ < ρ) (hz : ‖z‖ = ρ)
    (hρR : ρ ≤ R) :
    greenBall R x z ≤
      (4 * Real.pi)⁻¹ * ((R ^ 2 - ‖x‖ ^ 2) * (R ^ 2 - ρ ^ 2) / (R ^ 2 * (ρ - ‖x‖) ^ 2)) := by
  have hxR : ‖x‖ < R := hxρ.trans_le hρR
  have hxz : x ≠ z := by rintro rfl; exact hxρ.ne hz
  have ha := norm_sub_conj_mul_pos hR hxR (hz ▸ hρR)
  refine (greenBall_le hR hxz ha).trans ?_
  rw [hz]
  have hdist : ρ - ‖x‖ ≤ ‖x - z‖ := by
    have := norm_sub_norm_le z x
    rw [norm_sub_rev, hz] at this
    exact this
  have hP : 0 ≤ (R ^ 2 - ‖x‖ ^ 2) * (R ^ 2 - ρ ^ 2) :=
    mul_nonneg (by nlinarith [norm_nonneg x]) (by nlinarith [(norm_nonneg x).trans hxρ.le])
  have hpos : 0 < R ^ 2 * (ρ - ‖x‖) ^ 2 := by
    have : 0 < ρ - ‖x‖ := sub_pos.2 hxρ
    positivity
  have hDle : R ^ 2 * (ρ - ‖x‖) ^ 2 ≤ R ^ 2 * ‖x - z‖ ^ 2 := by
    have : 0 ≤ ρ - ‖x‖ := (sub_pos.2 hxρ).le
    gcongr
  gcongr

/-! ## The explicit greatest harmonic minorant -/

/-- The explicit greatest harmonic minorant of the Newtonian kernel `N(x,·)` on the disc `B_R(0)`,
`h_x(z) = -(2π)⁻¹ (log |R² - x̄ z| - log R)`: `N(x,·) - h_x = greenBall R x` off the pole
(`newtonKernel_sub_greenBall`) and `h_x = I_{B_R}[N(x,·)]` on `B_R(0)` (`greatestHarmonicMinorant_ball`). -/
noncomputable def greatestHarmonicMinorantBall (R : ℝ) (x z : ℂ) : ℝ :=
  -(2 * Real.pi)⁻¹ * (Real.log ‖(R : ℂ) ^ 2 - conj x * z‖ - Real.log R)

theorem newtonKernel_sub_greenBall {R : ℝ} (hR : 0 < R) {x z : ℂ} (hxz : x ≠ z)
    (hz : ‖(R : ℂ) ^ 2 - conj x * z‖ ≠ 0) :
    newtonKernel x z - greenBall R x z = greatestHarmonicMinorantBall R x z := by
  have hn : ‖x - z‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hxz)
  rw [newtonKernel, greenBall, greatestHarmonicMinorantBall, Real.log_div hz (mul_ne_zero hR.ne' hn),
    Real.log_mul hR.ne' hn]
  ring

/-- The Newtonian kernel `N(x,·)` is harmonic off its pole. -/
theorem harmonicAt_newtonKernel {x z : ℂ} (hz : z ≠ x) : HarmonicAt (newtonKernel x) z := by
  have ha : AnalyticAt ℂ (fun w => x - w) z := by fun_prop
  have h1 := (ha.harmonicAt_log_norm (sub_ne_zero.2 (Ne.symm hz))).const_smul (c := -(2 * Real.pi)⁻¹)
  convert h1 using 1
  funext w
  simp [newtonKernel, smul_eq_mul]

theorem harmonicAt_greatestHarmonicMinorantBall {R : ℝ} {x z : ℂ}
    (hz : (R : ℂ) ^ 2 - conj x * z ≠ 0) : HarmonicAt (greatestHarmonicMinorantBall R x) z := by
  have ha : AnalyticAt ℂ (fun w => (R : ℂ) ^ 2 - conj x * w) z := by fun_prop
  have h1 := ((ha.harmonicAt_log_norm hz).sub (harmonicAt_const (Real.log R))).const_smul
    (c := -(2 * Real.pi)⁻¹)
  convert h1 using 1
  funext w
  simp [greatestHarmonicMinorantBall, smul_eq_mul]

/-- `h_x` is a harmonic minorant of `N(x,·)` on `B_R(0)`, since `greenBall R x ≥ 0` there. -/
theorem isHarmonicMinorant_greatestHarmonicMinorantBall {R : ℝ} {x : ℂ} (hx : x ∈ ball (0 : ℂ) R) :
    IsHarmonicMinorant (ball 0 R) (newtonKernelEReal x) (greatestHarmonicMinorantBall R x) := by
  rw [mem_ball_zero_iff] at hx
  have hR : 0 < R := (norm_nonneg x).trans_lt hx
  refine ⟨fun z hz => harmonicAt_greatestHarmonicMinorantBall ?_, fun z hz => ?_⟩
  · rw [mem_ball_zero_iff] at hz
    exact norm_pos_iff.1 (norm_sub_conj_mul_pos hR hx hz.le)
  · by_cases hzx : z = x
    · simp [newtonKernelEReal, hzx]
    · rw [mem_ball_zero_iff] at hz
      simp only [newtonKernelEReal, hzx, ite_false, EReal.coe_le_coe_iff]
      rw [← newtonKernel_sub_greenBall hR (Ne.symm hzx) (norm_sub_conj_mul_pos hR hx hz.le).ne']
      linarith [greenBall_nonneg hR hx.le hz.le]

/-! ## The maximum principle on discs -/

/-- The maximum principle for harmonic functions on closed discs: if `f` is harmonic on `B_R(c)` and `f ≤ C` on the
circle `∂B_ρ(c)`, `0 < ρ < R`, then `f ≤ C` on `closedBall c ρ`. Proof: `f = Re F` with `F` holomorphic on `B_R(c)`,
and the maximum modulus principle for `exp ∘ F`. -/
theorem le_of_forall_mem_sphere_le_of_harmonicOnNhd {f : ℂ → ℝ} {c : ℂ} {R ρ : ℝ}
    (hf : HarmonicOnNhd f (ball c R)) (hρ : 0 < ρ) (hρR : ρ < R) {C : ℝ}
    (hC : ∀ z ∈ sphere c ρ, f z ≤ C) {y : ℂ} (hy : y ∈ closedBall c ρ) : f y ≤ C := by
  obtain ⟨F, hF, hFf⟩ := hf.exists_analyticOnNhd_ball_re_eq
  have hsub : closedBall c ρ ⊆ ball c R := closedBall_subset_ball hρR
  have hre : ∀ z ∈ closedBall c ρ, (F z).re = f z := fun z hz => hFf (hsub hz)
  have hd : DiffContOnCl ℂ (fun z => Complex.exp (F z)) (ball c ρ) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball c hρ.ne']
    intro z hz
    exact (hF z (hsub hz)).differentiableAt.cexp.differentiableWithinAt
  have key := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd (C := Real.exp C)
    (fun z hz => ?_) (by rwa [closure_ball c hρ.ne'])
  · rw [Complex.norm_exp, hre y hy] at key
    exact Real.exp_le_exp.1 key
  · rw [frontier_ball c hρ.ne'] at hz
    rw [Complex.norm_exp, hre z (sphere_subset_closedBall hz)]
    exact Real.exp_le_exp.2 (hC z hz)

/-! ## The Green function of a disc -/

/-- Every harmonic minorant `h` of `N(x,·)` on `B_R(0)` satisfies `h ≤ h_x` on `B_R(0)`. -/
theorem IsHarmonicMinorant.le_greatestHarmonicMinorantBall {R : ℝ} {x : ℂ} (hx : x ∈ ball (0 : ℂ) R)
    {h : ℂ → ℝ} (hh : IsHarmonicMinorant (ball 0 R) (newtonKernelEReal x) h) {y : ℂ}
    (hy : y ∈ ball (0 : ℂ) R) : h y ≤ greatestHarmonicMinorantBall R x y := by
  have hgh : HarmonicOnNhd (h - greatestHarmonicMinorantBall R x) (ball 0 R) :=
    hh.1.sub (isHarmonicMinorant_greatestHarmonicMinorantBall hx).1
  rw [mem_ball_zero_iff] at hx hy
  have hR : 0 < R := (norm_nonneg x).trans_lt hx
  have hr₀ : max ‖x‖ ‖y‖ < R := max_lt hx hy
  set B : ℝ → ℝ := fun ρ =>
    (4 * Real.pi)⁻¹ * ((R ^ 2 - ‖x‖ ^ 2) * (R ^ 2 - ρ ^ 2) / (R ^ 2 * (ρ - ‖x‖) ^ 2)) with hB_def
  have hgB : ∀ ρ ∈ Set.Ioo (max ‖x‖ ‖y‖) R, h y - greatestHarmonicMinorantBall R x y ≤ B ρ := by
    rintro ρ ⟨hρ₀, hρR⟩
    have hxρ : ‖x‖ < ρ := (le_max_left _ _).trans_lt hρ₀
    have hyρ : ‖y‖ < ρ := (le_max_right _ _).trans_lt hρ₀
    have hρ : 0 < ρ := (norm_nonneg x).trans_lt hxρ
    refine le_of_forall_mem_sphere_le_of_harmonicOnNhd hgh hρ hρR (fun z hz => ?_)
      (mem_closedBall_zero_iff.2 hyρ.le)
    rw [mem_sphere_zero_iff_norm] at hz
    have hzx : z ≠ x := by rintro rfl; exact hxρ.ne hz
    have hzR : ‖z‖ < R := hz ▸ hρR
    have hpos := norm_sub_conj_mul_pos hR hx hzR.le
    have h1 : h z ≤ newtonKernel x z := by
      have := hh.2 z (mem_ball_zero_iff.2 hzR)
      simpa [newtonKernelEReal, hzx] using this
    have h2 := newtonKernel_sub_greenBall hR (Ne.symm hzx) hpos.ne'
    have h3 := greenBall_le_of_norm_eq hR hxρ hz hρR.le
    simp only [Pi.sub_apply, hB_def]
    linarith
  have hB : Tendsto B (𝓝[<] R) (𝓝 0) := by
    have hden : R ^ 2 * (R - ‖x‖) ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hR.ne') (pow_ne_zero 2 (sub_ne_zero.2 hx.ne'))
    have hc : ContinuousAt B R :=
      continuousAt_const.mul (ContinuousAt.div (by fun_prop) (by fun_prop) hden)
    have h0 : B R = 0 := by simp [hB_def]
    rw [← h0]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have := ge_of_tendsto hB (eventually_of_mem (Ioo_mem_nhdsLT hr₀) hgB)
  linarith

/-- The greatest harmonic minorant of `N(x,·)` on `B_R(0)` is `h_x`. -/
theorem greatestHarmonicMinorant_ball {R : ℝ} {x y : ℂ} (hx : x ∈ ball (0 : ℂ) R)
    (hy : y ∈ ball (0 : ℂ) R) :
    greatestHarmonicMinorant (ball 0 R) (newtonKernelEReal x) y = greatestHarmonicMinorantBall R x y :=
  le_antisymm (iSup₂_le fun _ hh => EReal.coe_le_coe_iff.2 (hh.le_greatestHarmonicMinorantBall hx hy))
    ((isHarmonicMinorant_greatestHarmonicMinorantBall hx).le_greatestHarmonicMinorant y)

/-- **The Green function of a disc.** For `x, y ∈ B_R(0)`, `x ≠ y`,
`G_{B_R}(x,y) = (2π)⁻¹ log (|R² - x̄ y| / (R |x - y|))`. -/
theorem greenFunction_ball {R : ℝ} {x y : ℂ} (hx : x ∈ ball (0 : ℂ) R) (hy : y ∈ ball (0 : ℂ) R)
    (hxy : x ≠ y) : greenFunction (ball 0 R) x y = greenBall R x y := by
  have hR : 0 < R := (norm_nonneg x).trans_lt (mem_ball_zero_iff.1 hx)
  have hpos := norm_sub_conj_mul_pos hR (mem_ball_zero_iff.1 hx) (mem_ball_zero_iff.1 hy).le
  rw [greenFunction, ite_eq_left ⟨hx, hy, hxy⟩, greatestHarmonicMinorant_ball hx hy, EReal.toReal_coe]
  linarith [newtonKernel_sub_greenBall hR hxy hpos.ne']

/-! ## Corollaries: Proposition 2.3 for discs -/

theorem greenBall_comm (R : ℝ) (x y : ℂ) : greenBall R x y = greenBall R y x := by
  have : ‖(R : ℂ) ^ 2 - conj x * y‖ = ‖(R : ℂ) ^ 2 - conj y * x‖ := by
    rw [← Complex.norm_conj ((R : ℂ) ^ 2 - conj x * y)]
    congr 1
    simp only [map_sub, map_mul, map_pow, Complex.conj_ofReal, Complex.conj_conj]
    ring
  rw [greenBall, greenBall, this, norm_sub_rev x y]

/-- Symmetry of the Green function of a disc. -/
theorem greenFunction_ball_comm (R : ℝ) (x y : ℂ) :
    greenFunction (ball 0 R) x y = greenFunction (ball 0 R) y x := by
  by_cases h : x ∈ ball (0 : ℂ) R ∧ y ∈ ball (0 : ℂ) R ∧ x ≠ y
  · obtain ⟨hx, hy, hxy⟩ := h
    rw [greenFunction_ball hx hy hxy, greenFunction_ball hy hx (Ne.symm hxy), greenBall_comm]
  · have h' : ¬ (y ∈ ball (0 : ℂ) R ∧ x ∈ ball (0 : ℂ) R ∧ y ≠ x) :=
      fun ⟨a, b, c⟩ => h ⟨b, a, Ne.symm c⟩
    simp only [greenFunction, h, h', ite_false]

/-- Positivity of the Green function of a disc (Proposition 2.3, "Positive", line 484). -/
theorem greenFunction_ball_pos {R : ℝ} {x y : ℂ} (hx : x ∈ ball (0 : ℂ) R) (hy : y ∈ ball (0 : ℂ) R)
    (hxy : x ≠ y) : 0 < greenFunction (ball 0 R) x y := by
  have hR : 0 < R := (norm_nonneg x).trans_lt (mem_ball_zero_iff.1 hx)
  rw [greenFunction_ball hx hy hxy]
  exact greenBall_pos hR (mem_ball_zero_iff.1 hx) (mem_ball_zero_iff.1 hy) hxy

/-- `G_{B_R}(x,y) = 0` for `|y| ≥ R`, in particular on `∂B_R(0)` (Proposition 2.3, "Zero boundary", line 485;
the boundary values are attained continuously by `continuousOn_greenFunction_ball`). -/
theorem greenFunction_ball_of_le_norm {R : ℝ} {y : ℂ} (hy : R ≤ ‖y‖) (x : ℂ) :
    greenFunction (ball 0 R) x y = 0 :=
  greenFunction_of_notMem_right (by simpa using hy) x

/-- Off the pole, `G_{B_R}(x,z) = max (greenBall R x z) 0` for every `z ∈ ℂ`. -/
theorem greenFunction_ball_eq_max {R : ℝ} {x z : ℂ} (hx : x ∈ ball (0 : ℂ) R) (hz : z ≠ x) :
    greenFunction (ball 0 R) x z = max (greenBall R x z) 0 := by
  have hx' := mem_ball_zero_iff.1 hx
  have hR : 0 < R := (norm_nonneg x).trans_lt hx'
  by_cases hzR : ‖z‖ < R
  · rw [greenFunction_ball hx (mem_ball_zero_iff.2 hzR) (Ne.symm hz),
      max_eq_left (greenBall_nonneg hR hx'.le hzR.le)]
  · rw [not_lt] at hzR
    rw [greenFunction_ball_of_le_norm hzR, max_eq_right (greenBall_nonpos hR hx'.le hzR)]

/-- `G_{B_R}(x,·)` is continuous on `ℂ \ {x}`; with `greenFunction_ball_of_le_norm`, it tends to `0` at
`∂B_R(0)` (Proposition 2.3, "Zero boundary", line 485). -/
theorem continuousOn_greenFunction_ball {R : ℝ} {x : ℂ} (hx : x ∈ ball (0 : ℂ) R) :
    ContinuousOn (greenFunction (ball 0 R) x) {x}ᶜ := by
  have hx' := mem_ball_zero_iff.1 hx
  have hR : 0 < R := (norm_nonneg x).trans_lt hx'
  refine ContinuousOn.congr (f := fun z => max (greenBall R x z) 0) ?_
    (fun z hz => greenFunction_ball_eq_max hx hz)
  intro z hz
  have hzx : z ≠ x := hz
  by_cases hzR : ‖z‖ ≤ R
  · have ha := norm_sub_conj_mul_pos hR hx' hzR
    have hb : R * ‖x - z‖ ≠ 0 := mul_ne_zero hR.ne' (norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm hzx)))
    have hnum : ContinuousAt (fun w : ℂ => ‖(R : ℂ) ^ 2 - conj x * w‖) z := by fun_prop
    have hden : ContinuousAt (fun w : ℂ => R * ‖x - w‖) z := by fun_prop
    have hc : ContinuousAt (greenBall R x) z := by
      show ContinuousAt (fun w => (2 * Real.pi)⁻¹ * Real.log (‖(R : ℂ) ^ 2 - conj x * w‖ / (R * ‖x - w‖))) z
      exact continuousAt_const.mul ((hnum.div hden hb).log (div_ne_zero ha.ne' hb))
    exact ContinuousAt.continuousWithinAt (f := fun w => max (greenBall R x w) 0)
      (hc.max tendsto_const_nhds)
  · rw [not_le] at hzR
    have hev : (fun w => max (greenBall R x w) 0) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hzR] with w hw
      exact max_eq_right (greenBall_nonpos hR hx'.le hw.le)
    exact (continuousAt_const.congr hev.symm).continuousWithinAt

/-- `G_{B_R}(x,·)` is harmonic on `B_R(0) \ {x}`. -/
theorem harmonicOnNhd_greenFunction_ball {R : ℝ} {x : ℂ} (hx : x ∈ ball (0 : ℂ) R) :
    HarmonicOnNhd (greenFunction (ball 0 R) x) (ball 0 R \ {x}) := by
  have hx' := mem_ball_zero_iff.1 hx
  have hR : 0 < R := (norm_nonneg x).trans_lt hx'
  intro z hz
  have hopen : IsOpen (ball (0 : ℂ) R \ {x}) := isOpen_ball.sdiff isClosed_singleton
  have heq : greenFunction (ball 0 R) x =ᶠ[𝓝 z]
      newtonKernel x - greatestHarmonicMinorantBall R x := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    have hwx : w ≠ x := hw.2
    have hw' := mem_ball_zero_iff.1 hw.1
    rw [Pi.sub_apply, greenFunction_ball hx hw.1 (Ne.symm hwx),
      ← newtonKernel_sub_greenBall hR (Ne.symm hwx) (norm_sub_conj_mul_pos hR hx' hw'.le).ne']
    ring
  have hz' := mem_ball_zero_iff.1 hz.1
  exact (harmonicAt_congr_nhds heq).2 ((harmonicAt_newtonKernel hz.2).sub
    (harmonicAt_greatestHarmonicMinorantBall (norm_pos_iff.1 (norm_sub_conj_mul_pos hR hx' hz'.le))))

/-- `G_{B_R}(x,·)` is real analytic on `B_R(0) \ {x}`. -/
theorem analyticOnNhd_greenFunction_ball {R : ℝ} {x : ℂ} (hx : x ∈ ball (0 : ℂ) R) :
    AnalyticOnNhd ℝ (greenFunction (ball 0 R) x) (ball 0 R \ {x}) :=
  fun z hz => _root_.HarmonicAt.analyticAt (harmonicOnNhd_greenFunction_ball hx z hz)

/-- `G_{B_R}(x,·)` is infinitely differentiable (indeed `C^ω`) on `B_R(0) \ {x}` (Proposition 2.3, "Smooth away
from the pole", line 486). -/
theorem contDiffOn_greenFunction_ball {R : ℝ} {x : ℂ} (hx : x ∈ ball (0 : ℂ) R) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (greenFunction (ball 0 R) x) (ball 0 R \ {x}) :=
  fun z hz => (analyticOnNhd_greenFunction_ball hx z hz).contDiffAt.contDiffWithinAt

end HarmonicBalls
