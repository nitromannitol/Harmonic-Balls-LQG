/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Examples.HeatGenerator

/-! # Uniform Gaussian estimates for families of one-dimensional slices

The quantitative estimate below is adapted from the private proof in
`MarkovProcess.Examples.HeatGenerator`, by Scott Armstrong. It is restated
here to allow a bound uniform over a family of planar coordinate slices.
-/

namespace HarmonicBalls.Section6

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty

noncomputable section

/-- All polynomial moments of the standard normal law are finite. -/
private theorem integrable_pow_gaussian (n : ℕ) :
    Integrable (fun z : ℝ ↦ z ^ n) (gaussianReal 0 1) :=
  integrable_pow_of_mem_interior_integrableExpSet (by simp) n

/-- The first moment of the standard normal law vanishes. -/
private theorem integral_id_gaussian : ∫ z : ℝ, z ∂(gaussianReal 0 1) = 0 :=
  integral_id_gaussianReal

/-- The second moment of the standard normal law is one. -/
private theorem integral_sq_gaussian : ∫ z : ℝ, z ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have hvar : Var[fun z : ℝ ↦ z; gaussianReal 0 1] = ((1 : ℝ≥0) : ℝ) :=
    variance_fun_id_gaussianReal
  rw [variance_eq_integral (by fun_prop), integral_id_gaussianReal] at hvar
  simpa using hvar

/-- The fourth moment of the standard normal law. -/
def gaussianMoment4 : ℝ := ∫ z : ℝ, z ^ 4 ∂(gaussianReal 0 1)

private theorem gaussianMoment4_nonneg : 0 ≤ gaussianMoment4 :=
  integral_nonneg fun z ↦ by positivity

/-- The Gaussian average, read on the standard normal law. -/
private theorem integral_gaussian_eq (g : ℝ → ℝ) (hg : Continuous g) (x : ℝ) (t : ℝ≥0) :
    ∫ y, g y ∂gaussianReal x t = ∫ z, g (x + Real.sqrt t * z) ∂(gaussianReal 0 1) := by
  rw [MarkovProcess.gaussianReal_eq_map_add_sqrt_mul x t, integral_map (by fun_prop) hg.aestronglyMeasurable]


variable {f : ℝ → ℝ}

/-- A pure-algebra step: away from the origin a constant is dominated by a quadratic. -/
private theorem le_mul_sq_div {M a b : ℝ} (hM : 0 ≤ M) (hb : 0 < b) (hab : b ≤ |a|) :
    M ≤ M * a ^ 2 / b ^ 2 := by
  have hsq : b ^ 2 ≤ a ^ 2 := by nlinarith [sq_abs a, abs_nonneg a]
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **The quantitative estimate.**  If the second derivative of `f` is bounded by `M` and varies
by at most `ε` over distances smaller than `δ`, then the Gaussian difference quotient at scale
`t` differs from half the second derivative by at most `ε` plus a term of order `t`, uniformly
in the centre `x`. -/
theorem abs_gaussianQuotient_sub_le (hf : ContDiff ℝ 2 f) {B M ε δ : ℝ}
    (hB : ∀ y, |f y| ≤ B) (hM : ∀ y, |iteratedDeriv 2 f y| ≤ M) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hunif : ∀ u v : ℝ, |u - v| < δ → |iteratedDeriv 2 f u - iteratedDeriv 2 f v| ≤ ε)
    {t : ℝ≥0} (ht : 0 < (t : ℝ)) (x : ℝ) :
    |(t : ℝ)⁻¹ * (∫ y, f y ∂gaussianReal x t - f x) - iteratedDeriv 2 f x / 2| ≤
      ε + 2 * M * (t : ℝ) * gaussianMoment4 / δ ^ 2 := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM x)
  set σ := Real.sqrt (t : ℝ) with hσdef
  have hσ2 : σ ^ 2 = (t : ℝ) := Real.sq_sqrt t.coe_nonneg
  set c := iteratedDeriv 2 f x with hcdef
  have hcont : Continuous f := hf.continuous
  have hz1 : Integrable (fun z : ℝ ↦ z) (gaussianReal 0 1) := by
    simpa using integrable_pow_gaussian 1
  have hz2 : Integrable (fun z : ℝ ↦ z ^ 2) (gaussianReal 0 1) := integrable_pow_gaussian 2
  have hz4 : Integrable (fun z : ℝ ↦ z ^ 4) (gaussianReal 0 1) := integrable_pow_gaussian 4
  have hshift : Integrable (fun z : ℝ ↦ f (x + σ * z)) (gaussianReal 0 1) := by
    refine Integrable.mono' (integrable_const B)
      ((hcont.comp (by fun_prop)).aestronglyMeasurable) ?_
    filter_upwards with z
    simpa using hB (x + σ * z)
  have hchange : ∫ y, f y ∂gaussianReal x t = ∫ z, f (x + σ * z) ∂(gaussianReal 0 1) :=
    integral_gaussian_eq f hcont x t
  set E : ℝ → ℝ :=
    fun z ↦ f (x + σ * z) - f x - σ * z * deriv f x - (σ * z) ^ 2 / 2 * c with hEdef
  have h1 : Integrable (fun z : ℝ ↦ σ * z * deriv f x) (gaussianReal 0 1) := by
    have h := hz1.const_mul (σ * deriv f x)
    have heq : (fun z : ℝ ↦ σ * deriv f x * z) = fun z : ℝ ↦ σ * z * deriv f x := by
      funext z; ring
    rwa [heq] at h
  have h2 : Integrable (fun z : ℝ ↦ (σ * z) ^ 2 / 2 * c) (gaussianReal 0 1) := by
    have h := hz2.const_mul (σ ^ 2 * c / 2)
    have heq : (fun z : ℝ ↦ σ ^ 2 * c / 2 * z ^ 2) = fun z : ℝ ↦ (σ * z) ^ 2 / 2 * c := by
      funext z; ring
    rwa [heq] at h
  have hEint : Integrable E (gaussianReal 0 1) :=
    ((hshift.sub (integrable_const (f x))).sub h1).sub h2
  have hI1 : ∫ z : ℝ, σ * z * deriv f x ∂(gaussianReal 0 1) = 0 := by
    have heq : (fun z : ℝ ↦ σ * z * deriv f x) = fun z : ℝ ↦ σ * deriv f x * z := by
      funext z; ring
    rw [heq, integral_const_mul, integral_id_gaussian, mul_zero]
  have hI2 : ∫ z : ℝ, (σ * z) ^ 2 / 2 * c ∂(gaussianReal 0 1) = (t : ℝ) * c / 2 := by
    have heq : (fun z : ℝ ↦ (σ * z) ^ 2 / 2 * c) = fun z : ℝ ↦ σ ^ 2 * c / 2 * z ^ 2 := by
      funext z; ring
    rw [heq, integral_const_mul, integral_sq_gaussian, mul_one, hσ2]
  have hE : ∫ z, E z ∂(gaussianReal 0 1)
      = (∫ z, f (x + σ * z) ∂(gaussianReal 0 1)) - f x - (t : ℝ) * c / 2 := by
    have e1 : ∫ z, E z ∂(gaussianReal 0 1)
        = (∫ z, (f (x + σ * z) - f x - σ * z * deriv f x) ∂(gaussianReal 0 1))
          - ∫ z, ((σ * z) ^ 2 / 2 * c) ∂(gaussianReal 0 1) :=
      integral_sub ((hshift.sub (integrable_const (f x))).sub h1) h2
    have e2 : ∫ z, (f (x + σ * z) - f x - σ * z * deriv f x) ∂(gaussianReal 0 1)
        = (∫ z, (f (x + σ * z) - f x) ∂(gaussianReal 0 1))
          - ∫ z, (σ * z * deriv f x) ∂(gaussianReal 0 1) :=
      integral_sub (hshift.sub (integrable_const (f x))) h1
    have e3 : ∫ z, (f (x + σ * z) - f x) ∂(gaussianReal 0 1)
        = (∫ z, f (x + σ * z) ∂(gaussianReal 0 1)) - ∫ _z : ℝ, f x ∂(gaussianReal 0 1) :=
      integral_sub hshift (integrable_const (f x))
    have e4 : ∫ _z : ℝ, f x ∂(gaussianReal 0 1) = f x := by simp
    rw [e1, e2, e3, e4, hI1, hI2]
    ring
  have hEbound : ∀ z : ℝ,
      |E z| ≤ ε * (t : ℝ) * z ^ 2 + 2 * M * (t : ℝ) ^ 2 / δ ^ 2 * z ^ 4 := by
    intro z
    have hCbound : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        |iteratedDeriv 2 f (x + s * (σ * z)) - iteratedDeriv 2 f x| ≤
          ε + 2 * M * (σ * z) ^ 2 / δ ^ 2 := by
      intro s hs
      rcases lt_or_ge |σ * z| δ with hlt | hge
      · have hclose : |x + s * (σ * z) - x| < δ := by
          rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hs.1]
          calc s * |σ * z| ≤ 1 * |σ * z| :=
                mul_le_mul_of_nonneg_right hs.2 (abs_nonneg _)
            _ = |σ * z| := one_mul _
            _ < δ := hlt
        have hpos : 0 ≤ 2 * M * (σ * z) ^ 2 / δ ^ 2 := by positivity
        linarith [hunif _ _ hclose]
      · have habs : |iteratedDeriv 2 f (x + s * (σ * z)) - iteratedDeriv 2 f x| ≤ 2 * M := by
          calc |iteratedDeriv 2 f (x + s * (σ * z)) - iteratedDeriv 2 f x|
              ≤ |iteratedDeriv 2 f (x + s * (σ * z))| + |iteratedDeriv 2 f x| := abs_sub _ _
            _ ≤ M + M := add_le_add (hM _) (hM _)
            _ = 2 * M := by ring
        have hstep : 2 * M ≤ 2 * M * (σ * z) ^ 2 / δ ^ 2 :=
          le_mul_sq_div (by linarith) hδ hge
        linarith
    have htaylor := MarkovProcess.abs_sub_taylor_two_le hf x (σ * z) _ hCbound
    refine le_trans htaylor (le_of_eq ?_)
    have hsq : (σ * z) ^ 2 = (t : ℝ) * z ^ 2 := by rw [mul_pow, hσ2]
    rw [hsq]
    field_simp
  have hboundInt : Integrable
      (fun z : ℝ ↦ ε * (t : ℝ) * z ^ 2 + 2 * M * (t : ℝ) ^ 2 / δ ^ 2 * z ^ 4)
      (gaussianReal 0 1) := (hz2.const_mul _).add (hz4.const_mul _)
  have hIabs : |∫ z, E z ∂(gaussianReal 0 1)| ≤
      ε * (t : ℝ) + 2 * M * (t : ℝ) ^ 2 / δ ^ 2 * gaussianMoment4 := by
    calc |∫ z, E z ∂(gaussianReal 0 1)| ≤ ∫ z, |E z| ∂(gaussianReal 0 1) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z, (ε * (t : ℝ) * z ^ 2 + 2 * M * (t : ℝ) ^ 2 / δ ^ 2 * z ^ 4) ∂(gaussianReal 0 1) :=
          integral_mono hEint.abs hboundInt hEbound
      _ = ε * (t : ℝ) + 2 * M * (t : ℝ) ^ 2 / δ ^ 2 * gaussianMoment4 := by
          rw [integral_add (hz2.const_mul _) (hz4.const_mul _), integral_const_mul,
            integral_const_mul, integral_sq_gaussian, mul_one, gaussianMoment4]
  have hkey : (t : ℝ)⁻¹ * (∫ y, f y ∂gaussianReal x t - f x) - c / 2
      = (t : ℝ)⁻¹ * ∫ z, E z ∂(gaussianReal 0 1) := by
    rw [hchange, hE]
    field_simp
  rw [hkey, abs_mul, abs_of_nonneg (inv_nonneg.mpr ht.le)]
  calc (t : ℝ)⁻¹ * |∫ z, E z ∂(gaussianReal 0 1)|
      ≤ (t : ℝ)⁻¹ * (ε * (t : ℝ) + 2 * M * (t : ℝ) ^ 2 / δ ^ 2 * gaussianMoment4) :=
        mul_le_mul_of_nonneg_left hIabs (inv_nonneg.mpr ht.le)
    _ = ε + 2 * M * (t : ℝ) * gaussianMoment4 / δ ^ 2 := by
        field_simp


/-- Gaussian difference quotients converge uniformly over a family whose
second derivatives have a common bound and modulus of continuity. -/
theorem tendstoUniformly_gaussianQuotient_family {ι : Type*} {F : ι → ℝ → ℝ}
    (hF : ∀ i, ContDiff ℝ 2 (F i)) {B M : ℝ} (hMnn : 0 ≤ M)
    (hB : ∀ i y, |F i y| ≤ B) (hM : ∀ i y, |iteratedDeriv 2 (F i) y| ≤ M)
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (i : ι) (u v : ℝ),
      |u - v| < δ → |iteratedDeriv 2 (F i) u - iteratedDeriv 2 (F i) v| ≤ ε) :
    TendstoUniformly
      (fun (t : ℝ≥0) (p : ι × ℝ) => (t : ℝ)⁻¹ *
        (∫ y, F p.1 y ∂gaussianReal p.2 t - F p.1 p.2))
      (fun p => iteratedDeriv 2 (F p.1) p.2 / 2) (𝓝[>] 0) := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hmod (ε / 2) (by linarith)
  have hKnn : 0 ≤ 2 * M * gaussianMoment4 :=
    mul_nonneg (by linarith) gaussianMoment4_nonneg
  have hK : 0 < 2 * M * gaussianMoment4 + 1 := by linarith
  set T : ℝ := ε * δ ^ 2 / (2 * (2 * M * gaussianMoment4 + 1)) with hT
  have hTpos : 0 < T := div_pos (mul_pos hε (pow_pos hδ 2)) (by linarith)
  have hev : ∀ᶠ t : ℝ≥0 in 𝓝[>] 0, (t : ℝ) < T := by
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ) < T} :=
      isOpen_lt NNReal.continuous_coe continuous_const
    have hmem : (0 : ℝ≥0) ∈ {t : ℝ≥0 | (t : ℝ) < T} := by simpa using hTpos
    exact mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hmem)
  filter_upwards [hev, self_mem_nhdsWithin] with t htT htpos
  intro ⟨i, x⟩
  have htpos' : (0 : ℝ) < (t : ℝ) := NNReal.coe_pos.mpr htpos
  have hmain := abs_gaussianQuotient_sub_le (hF i) (hB i) (hM i)
    (by linarith : (0 : ℝ) ≤ ε / 2) hδ (hδ' i) htpos' x
  rw [Real.dist_eq, abs_sub_comm]
  refine lt_of_le_of_lt hmain ?_
  have hKt : (2 * M * gaussianMoment4 + 1) * (t : ℝ)
      < (2 * M * gaussianMoment4 + 1) * T := mul_lt_mul_of_pos_left htT hK
  have hTval : (2 * M * gaussianMoment4 + 1) * T = ε * δ ^ 2 / 2 := by
    rw [hT]; field_simp
  have hprod : 2 * M * gaussianMoment4 * (t : ℝ) < ε * δ ^ 2 / 2 := by
    nlinarith [hKt, hTval, htpos'.le]
  have hbound : 2 * M * (t : ℝ) * gaussianMoment4 / δ ^ 2 < ε / 2 := by
    rw [div_lt_iff₀ (pow_pos hδ 2)]
    nlinarith [hprod]
  linarith

end
end HarmonicBalls.Section6
