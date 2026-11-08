import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.RouteACircleSymmetry

/-! # Route (A), C3 (deterministic core): Fubini identity for circle averages

For continuous compactly supported `F, ψ : ℂ → ℝ` and `R : ℝ`:
`∫ z, ψ z * ⨍_{∂B(z,R)} F = ∫ x, F x * ⨍_{∂B(x,-R)} ψ`, with `⨍` the circle average `Real.circleAverage`.
This is the symmetry of the circle-average kernel: Fubini in the variables `(z, θ)` and `(x, θ)`, with the translation
`z ↦ z + circleMap 0 R θ`. It identifies `∫ hcirc(r, z) ψ(z) dz` with the pairing of the smoothed test function
`x ↦ ⨍_{∂B(x,r)} ψ` (route (A) of r8; the circle-average identity of C3 is the random version, not in this file).
Integrability is `integrable_prod_volume_restrict_Icc` (RouteACircleSymmetry.lean).
-/

noncomputable section

open MeasureTheory Set Metric Complex Real
open scoped ENNReal

namespace HarmonicBalls

/-- The Fubini identity for circle averages (deterministic core of C3). -/
theorem integral_mul_circleAverage_symm {F ψ : ℂ → ℝ} (hF : Continuous F) (hψ : Continuous ψ)
    (hFc : HasCompactSupport F) (hψc : HasCompactSupport ψ) (R : ℝ) :
    ∫ z, ψ z * Real.circleAverage F z R = ∫ x, F x * Real.circleAverage ψ x (-R) := by
  have hcm : Continuous fun p : ℂ × ℝ => circleMap p.1 R p.2 := by
    unfold circleMap
    fun_prop
  have hcm0 : Continuous fun θ : ℝ => circleMap 0 R θ := by
    unfold circleMap
    fun_prop
  -- the integrand of the first Fubini identity
  set g₁ : ℂ × ℝ → ℝ := fun p => (2 * π)⁻¹ * (ψ p.1 * F (circleMap p.1 R p.2)) with hg₁
  have hg₁c : Continuous g₁ := by
    rw [hg₁]
    exact continuous_const.mul ((hψ.comp continuous_fst).mul (hF.comp hcm))
  have hg₁K : ∀ p : ℂ × ℝ, p.1 ∉ tsupport ψ → g₁ p = 0 := by
    intro p hp
    simp [hg₁, image_eq_zero_of_notMem_tsupport hp]
  -- step 1: the circle average as an integral over `Icc 0 (2π)`
  have hstep1 : ∀ z : ℂ, ψ z * Real.circleAverage F z R = ∫ θ in Icc 0 (2 * π), g₁ (z, θ) := by
    intro z
    rw [Real.circleAverage, smul_eq_mul, intervalIntegral.integral_of_le (by positivity),
      integral_Icc_eq_integral_Ioc]
    simp only [hg₁]
    rw [integral_const_mul, integral_const_mul]
    ring
  -- step 2: exchange the order of `z` and `θ`
  have hint₁ : Integrable (Function.uncurry fun (z : ℂ) (θ : ℝ) => g₁ (z, θ))
      ((volume : Measure ℂ).prod (volume.restrict (Icc 0 (2 * π)))) :=
    integrable_prod_volume_restrict_Icc hψc.isCompact hg₁c hg₁K
  have hswap₁ : ∫ z, ∫ θ in Icc 0 (2 * π), g₁ (z, θ)
      = ∫ θ in Icc 0 (2 * π), ∫ z, g₁ (z, θ) :=
    integral_integral_swap hint₁
  -- step 3: translation in `z` for fixed `θ`
  have hstep3 : ∀ θ : ℝ, ∫ z, g₁ (z, θ) = (2 * π)⁻¹ * ∫ x, ψ (x - circleMap 0 R θ) * F x := by
    intro θ
    have hpt : ∀ z : ℂ, g₁ (z, θ) = (2 * π)⁻¹ * (ψ z * F (z + circleMap 0 R θ)) := fun z => by
      have hz : circleMap z R θ = z + circleMap 0 R θ := by simp [circleMap]
      simp only [hg₁, hz]
    have hsh : ∫ z : ℂ, ψ z * F (z + circleMap 0 R θ) = ∫ x : ℂ, ψ (x - circleMap 0 R θ) * F x := by
      have h : ∫ x : ℂ, ψ (x + circleMap 0 R θ - circleMap 0 R θ) * F (x + circleMap 0 R θ)
          = ∫ x : ℂ, ψ (x - circleMap 0 R θ) * F x :=
        integral_add_right_eq_self (fun x : ℂ => ψ (x - circleMap 0 R θ) * F x) (circleMap 0 R θ)
      simp only [add_sub_cancel_right] at h
      exact h
    simp only [hpt]
    rw [integral_const_mul, hsh]
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  -- step 4: the second integrand, `H(x, θ) = (2π)⁻¹ ψ(x - circleMap 0 R θ) F x`
  set H : ℂ × ℝ → ℝ := fun p => (2 * π)⁻¹ * (ψ (p.1 - circleMap 0 R p.2) * F p.1) with hH
  have hHc : Continuous H := by
    rw [hH]
    exact continuous_const.mul
      ((hψ.comp (continuous_fst.sub (hcm0.comp continuous_snd))).mul (hF.comp continuous_fst))
  have hHK : ∀ p : ℂ × ℝ, p.1 ∉ tsupport F → H p = 0 := by
    intro p hp
    simp [hH, image_eq_zero_of_notMem_tsupport hp]
  have hH1 : Integrable H ((volume : Measure ℂ).prod (volume.restrict (Icc 0 (2 * π)))) :=
    integrable_prod_volume_restrict_Icc hFc.isCompact hHc hHK
  have hHint : Integrable (Function.uncurry fun (θ : ℝ) (x : ℂ) => H (x, θ))
      ((volume.restrict (Icc 0 (2 * π))).prod (volume : Measure ℂ)) := hH1.swap
  have hswap₂ : ∫ θ in Icc 0 (2 * π), ∫ x, H (x, θ)
      = ∫ x, ∫ θ in Icc 0 (2 * π), H (x, θ) :=
    integral_integral_swap hHint
  -- step 5: the θ-integral of `H(x, ·)` is `F x` times the circle average of ψ at radius `-R`
  have hinner : ∀ x : ℂ, ∫ θ in Icc 0 (2 * π), H (x, θ) = F x * Real.circleAverage ψ x (-R) := by
    intro x
    have hcirc : ∀ θ : ℝ, circleMap x (-R) θ = x - circleMap 0 R θ := fun θ => by
      simp [circleMap]
      ring
    calc ∫ θ in Icc 0 (2 * π), H (x, θ)
        = ∫ θ in Icc 0 (2 * π), F x * ((2 * π)⁻¹ * ψ (circleMap x (-R) θ)) := by
          congr 1
          funext θ
          simp only [hH, hcirc θ]
          ring
      _ = F x * ∫ θ in Icc 0 (2 * π), (2 * π)⁻¹ * ψ (circleMap x (-R) θ) := integral_const_mul _ _
      _ = F x * ((2 * π)⁻¹ * ∫ θ in Icc 0 (2 * π), ψ (circleMap x (-R) θ)) := by
          rw [integral_const_mul]
      _ = F x * Real.circleAverage ψ x (-R) := by
          rw [Real.circleAverage, smul_eq_mul, intervalIntegral.integral_of_le h2π,
            integral_Icc_eq_integral_Ioc]
  -- step 6: combine the four identities
  calc ∫ z, ψ z * Real.circleAverage F z R
      = ∫ z, ∫ θ in Icc 0 (2 * π), g₁ (z, θ) := by
        congr 1
        funext z
        exact hstep1 z
    _ = ∫ θ in Icc 0 (2 * π), ∫ z, g₁ (z, θ) := hswap₁
    _ = ∫ θ in Icc 0 (2 * π), ∫ x, H (x, θ) := by
        congr 1
        funext θ
        rw [hstep3 θ, ← integral_const_mul]
    _ = ∫ x, ∫ θ in Icc 0 (2 * π), H (x, θ) := hswap₂
    _ = ∫ x, F x * Real.circleAverage ψ x (-R) := by
        congr 1
        funext x
        exact hinner x

end HarmonicBalls

end
