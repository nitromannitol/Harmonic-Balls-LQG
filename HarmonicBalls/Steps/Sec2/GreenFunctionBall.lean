import HarmonicBalls.Draft.Section2
import HarmonicBalls.Proofs.Potential.GreenBall
import HarmonicBalls.Proofs.Potential.Fundamental

/-!
# Proposition 2.3: the Green function of a disc

Proof of `GreenFunctionBallStmt` (Proposition 2.3, prop:green-properties, line 480 of
paper/lqg_harmonic_ball-corrected.tex).

## Steps

* `NewtonKernelFundamentalSolution`: `∫ N(x,y) Δφ(y) dy = -φ(x)` for compactly supported `C²` functions `φ`, i.e.
  `ΔN(x,·) = -δ_x` on the plane (HarmonicBalls/Proofs/Potential/Fundamental.lean,
  `integral_newtonKernel_mul_laplacian`).
* `greenFunctionBall_of_steps`: on `B_R(0) \ {x}`, `G_{B_R}(x,·) = N(x,·) - h_x` with
  `h_x(y) = -(2π)⁻¹ (log |R² - x̄ y| - log R)` (`greatestHarmonicMinorantBall`, HarmonicBalls/Proofs/Potential/
  GreenBall.lean). For `x ≠ 0`, `h_x = c + N(x*,·)` off the reflected point `x* = R² / x̄ ∉ closure B_R(0)`, and
  for `x = 0` it is constant; hence `∫ h_x Δφ = c ∫ Δφ - φ(x*) = 0` for test functions `φ` on `B_R(0)`, and
  `∫ G Δφ = ∫ N(x,·) Δφ = -φ(x)`. Positivity, the zero boundary values and smoothness off the pole are the
  corollaries of the explicit formula in GreenBall.lean.
-/

namespace HarmonicBalls

open MeasureTheory Metric Filter Topology Set Laplacian ComplexConjugate
open scoped ContDiff

/-- Step of Proposition 2.3: the Newtonian kernel `N(x,·)` is a fundamental solution of `-Δ` on the plane,
`ΔN(x,·) = -δ_x`, tested against compactly supported `C²` functions. -/
def NewtonKernelFundamentalSolution : Prop :=
  ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → ∀ x : ℂ, ∫ y, newtonKernel x y * Δ φ y = -φ x

theorem newtonKernelFundamentalSolution : NewtonKernelFundamentalSolution :=
  fun _ hφ hc x => integral_newtonKernel_mul_laplacian hφ hc x

/-- The harmonic part `h_x` of `G_{B_R}(x,·)` is, off the reflected point `x* = R² / x̄`, a constant plus the
Newtonian kernel with pole `x*`. -/
theorem greatestHarmonicMinorantBall_eq {R : ℝ} {x : ℂ} (hx0 : x ≠ 0) {y : ℂ}
    (hy : y ≠ (R : ℂ) ^ 2 / conj x) :
    greatestHarmonicMinorantBall R x y =
      -(2 * Real.pi)⁻¹ * (Real.log ‖x‖ - Real.log R) + newtonKernel ((R : ℂ) ^ 2 / conj x) y := by
  have hc : conj x ≠ 0 := (map_ne_zero _).2 hx0
  have h1 : (R : ℂ) ^ 2 - conj x * y = conj x * ((R : ℂ) ^ 2 / conj x - y) := by
    field_simp
  have h2 : ‖(R : ℂ) ^ 2 / conj x - y‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hy.symm)
  rw [greatestHarmonicMinorantBall, newtonKernel, h1, norm_mul, Complex.norm_conj,
    Real.log_mul (norm_ne_zero_iff.2 hx0) h2]
  ring

theorem norm_reflect_gt {R : ℝ} {x : ℂ} (hx : x ∈ ball (0 : ℂ) R) (hx0 : x ≠ 0) :
    R < ‖(R : ℂ) ^ 2 / conj x‖ := by
  rw [mem_ball_zero_iff] at hx
  have hR : 0 < R := (norm_nonneg x).trans_lt hx
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  rw [norm_div, Complex.norm_conj, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
    lt_div_iff₀ hn]
  nlinarith

/-- `h_x` is locally integrable, and `∫ h_x Δφ = 0` for every test function `φ` on `B_R(0)`. -/
theorem greatestHarmonicMinorantBall_weak (hN : NewtonKernelFundamentalSolution) {R : ℝ} {x : ℂ}
    (hx : x ∈ ball (0 : ℂ) R) :
    LocallyIntegrable (greatestHarmonicMinorantBall R x) ∧
      ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 R →
        ∫ y, greatestHarmonicMinorantBall R x y * Δ φ y = 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · have hconst : greatestHarmonicMinorantBall R 0 =
        fun _ => -(2 * Real.pi)⁻¹ * (Real.log ‖(R : ℂ) ^ 2‖ - Real.log R) := by
      funext y; simp [greatestHarmonicMinorantBall]
    rw [hconst]
    refine ⟨locallyIntegrable_const _, fun φ hφ hc _ => ?_⟩
    rw [integral_const_mul, integral_laplacian_eq_zero hφ hc, mul_zero]
  · set xs : ℂ := (R : ℂ) ^ 2 / conj x
    set c : ℝ := -(2 * Real.pi)⁻¹ * (Real.log ‖x‖ - Real.log R)
    have hae : (fun y => c + newtonKernel xs y) =ᵐ[volume] greatestHarmonicMinorantBall R x := by
      filter_upwards [ae_ne_complex xs] with y hy
      exact (greatestHarmonicMinorantBall_eq hx0 hy).symm
    have hli : LocallyIntegrable (greatestHarmonicMinorantBall R x) :=
      ((locallyIntegrable_const c).add (locallyIntegrable_newtonKernel xs)).congr hae
    refine ⟨hli, fun φ hφ hc hsupp => ?_⟩
    have hΔ := continuous_laplacian_of_contDiff hφ
    have hΔc := hasCompactSupport_laplacian hc
    have hxs : φ xs = 0 := image_eq_zero_of_notMem_tsupport fun h => by
      have := mem_ball_zero_iff.1 (hsupp h)
      linarith [norm_reflect_gt hx hx0]
    have i1 : Integrable fun y => c * Δ φ y :=
      (hΔ.integrable_of_hasCompactSupport hΔc).const_mul c
    have i2 : Integrable fun y => newtonKernel xs y * Δ φ y := by
      simpa [smul_eq_mul, mul_comm] using
        (locallyIntegrable_newtonKernel xs).integrable_smul_left_of_hasCompactSupport hΔ hΔc
    calc ∫ y, greatestHarmonicMinorantBall R x y * Δ φ y
        = ∫ y, (c * Δ φ y + newtonKernel xs y * Δ φ y) := by
          refine integral_congr_ae ?_
          filter_upwards [hae] with y hy
          rw [← hy]; ring
      _ = 0 := by
          rw [integral_add i1 i2, integral_const_mul, integral_laplacian_eq_zero hφ hc, hN φ hφ hc xs,
            hxs]
          ring

/-- **Proposition 2.3** from the fundamental-solution step. -/
theorem greenFunctionBall_of_steps (hN : NewtonKernelFundamentalSolution) : GreenFunctionBallStmt := by
  intro R hR x hx
  set G := greenFunction (ball (0 : ℂ) R) x with hG
  obtain ⟨hHli, hHΔ⟩ := greatestHarmonicMinorantBall_weak hN hx
  have hxR : ‖x‖ < R := mem_ball_zero_iff.1 hx
  -- `G = N(x,·) - h_x` on `B_R(0) \ {x}`
  have hGeq : ∀ y ∈ ball (0 : ℂ) R, y ≠ x →
      G y = newtonKernel x y - greatestHarmonicMinorantBall R x y := by
    intro y hy hyx
    rw [hG, greenFunction_ball hx hy (Ne.symm hyx), ← newtonKernel_sub_greenBall hR (Ne.symm hyx)
      (norm_sub_conj_mul_pos hR hxR (mem_ball_zero_iff.1 hy).le).ne']
    ring
  refine ⟨⟨?_, fun φ hφ => ?_⟩, fun y hy hyx => greenFunction_ball_pos hx hy (Ne.symm hyx),
    fun y hy => ⟨?_, ?_⟩, contDiffOn_greenFunction_ball hx⟩
  · -- local integrability on the disc
    refine (((locallyIntegrable_newtonKernel x).sub hHli).locallyIntegrableOn _).congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
    filter_upwards [ae_ne_complex x] with y hyx hy
    exact (hGeq y hy hyx).symm
  · -- the distributional identity `ΔG = -δ_x`
    obtain ⟨hφs, hφc, hφsupp⟩ := hφ
    have hφ2 : ContDiff ℝ 2 φ := hφs.of_le (by simp)
    have hΔ := continuous_laplacian_of_contDiff hφ2
    have hΔc := hasCompactSupport_laplacian hφc
    refine ⟨integrable_zero_measure, hφs.continuous.integrable_of_hasCompactSupport hφc, ?_⟩
    have i1 : Integrable fun y => newtonKernel x y * Δ φ y := by
      simpa [smul_eq_mul, mul_comm] using
        (locallyIntegrable_newtonKernel x).integrable_smul_left_of_hasCompactSupport hΔ hΔc
    have i2 : Integrable fun y => greatestHarmonicMinorantBall R x y * Δ φ y := by
      simpa [smul_eq_mul, mul_comm] using hHli.integrable_smul_left_of_hasCompactSupport hΔ hΔc
    have hΔ0 : ∀ y ∉ ball (0 : ℂ) R, Δ φ y = 0 := fun y hy =>
      image_eq_zero_of_notMem_tsupport fun h => hy (hφsupp (tsupport_laplacian_subset φ h))
    calc ∫ y, G y * Δ φ y
        = ∫ y, (newtonKernel x y * Δ φ y - greatestHarmonicMinorantBall R x y * Δ φ y) := by
          refine integral_congr_ae ?_
          filter_upwards [ae_ne_complex x] with y hyx
          by_cases hy : y ∈ ball (0 : ℂ) R
          · rw [hGeq y hy hyx]; ring
          · rw [hΔ0 y hy]; ring
      _ = ∫ y, φ y ∂(0 : Measure ℂ) - ∫ y, φ y ∂(Measure.dirac x) := by
          rw [integral_sub i1 i2, hN φ hφ2 hφc x, hHΔ φ hφ2 hφc hφsupp, integral_zero_measure,
            integral_dirac]
          ring
  · exact greenFunction_ball_of_le_norm (mem_sphere_zero_iff_norm.1 hy).ge x
  · have hyx : y ∈ ({x}ᶜ : Set ℂ) := fun h => by
      rw [mem_singleton_iff] at h
      rw [h, mem_sphere_zero_iff_norm] at hy
      linarith
    have hcont := ((continuousOn_greenFunction_ball hx).continuousAt
      (isOpen_compl_singleton.mem_nhds hyx)).tendsto
    rw [greenFunction_ball_of_le_norm (mem_sphere_zero_iff_norm.1 hy).ge x] at hcont
    exact hcont.mono_left nhdsWithin_le_nhds

/-- **Proposition 2.3** (prop:green-properties, line 480). -/
theorem greenFunctionBall : GreenFunctionBallStmt :=
  greenFunctionBall_of_steps newtonKernelFundamentalSolution

end HarmonicBalls
