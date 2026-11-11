import Mathlib

/-! # Route (A): smoothness of circle averages of test functions

For a smooth compactly supported `f : ℂ → E` and a continuous parametrization `g : ℝ → ℂ` (for the circle average,
`g θ = circleMap 0 R θ`), the function `y ↦ ∫ θ ∈ (0, 2π], f (y + g θ)` is `C^∞`, with derivative
`∫ θ, fderiv f (y + g θ)`. In particular the circle average `Real.circleAverage f · R` of a test function is smooth
with compact support; this is the smoothness of the smoothed test functions `ψ_r` and of
the mollified circle codes. Proof: differentiation under the integral sign
(`hasFDerivAt_integral_of_dominated_of_fderiv_le`) and induction on the order.
-/

noncomputable section

open MeasureTheory Set Metric Real
open scoped Topology ContDiff

namespace HarmonicBalls

/-- The derivative of `y ↦ ∫ θ ∈ (0, 2π], f (y + g θ)` (differentiation under the integral sign). -/
theorem hasFDerivAt_translate_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℂ → E} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) {g : ℝ → ℂ}
    (hg : Continuous g) (x : ℂ) :
    HasFDerivAt (fun y : ℂ => ∫ θ in Ioc (0 : ℝ) (2 * π), f (y + g θ))
      (∫ θ in Ioc (0 : ℝ) (2 * π), fderiv ℝ f (x + g θ)) x := by
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hf1 : Differentiable ℝ f := (contDiff_infty_iff_fderiv.1 hf).1
  have hfd : Continuous (fderiv ℝ f) := (contDiff_infty_iff_fderiv.1 hf).2.continuous
  have hfcs : HasCompactSupport (fderiv ℝ f) := HasCompactSupport.fderiv (𝕜 := ℝ) hfc
  obtain ⟨C, hC⟩ := hfd.bounded_above_of_compact_support hfcs
  have hcont : ∀ y : ℂ, Continuous (fun θ : ℝ => f (y + g θ)) :=
    fun y => hf1.continuous.comp (continuous_const.add hg)
  have hcont' : ∀ y : ℂ, Continuous (fun θ : ℝ => fderiv ℝ f (y + g θ)) :=
    fun y => hfd.comp (continuous_const.add hg)
  have hint : Integrable (fun θ : ℝ => f (x + g θ)) (volume.restrict (Ioc (0 : ℝ) (2 * π))) :=
    ((hcont x).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hdiff : ∀ θ : ℝ, ∀ y : ℂ, HasFDerivAt (fun z : ℂ => f (z + g θ)) (fderiv ℝ f (y + g θ)) y := by
    intro θ y
    have h1 := ((hf1 (y + g θ)).hasFDerivAt).comp y ((hasFDerivAt_id y).add_const (g θ))
    simpa [Function.comp_def] using h1
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict (Ioc (0 : ℝ) (2 * π)))
    (s := univ) (F' := fun y θ => fderiv ℝ f (y + g θ)) Filter.univ_mem
    (Filter.Eventually.of_forall fun y => (hcont y).aestronglyMeasurable) hint
    (hcont' x).aestronglyMeasurable (ae_of_all _ fun θ y _ => hC (y + g θ)) (integrable_const C)
    (ae_of_all _ fun θ y _ => hdiff θ y)

/-- Smoothness of parametric translation integrals: induction on the order of differentiation. -/
theorem contDiff_translate_integral (g : ℝ → ℂ) (hg : Continuous g) (n : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : ℂ → E),
      ContDiff ℝ ∞ f → HasCompactSupport f →
        ContDiff ℝ n (fun y : ℂ => ∫ θ in Ioc (0 : ℝ) (2 * π), f (y + g θ)) := by
  induction n with
  | zero =>
    intro E _ _ _ f hf hfc
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun x =>
      (hasFDerivAt_translate_integral hf hfc hg x).continuousAt
  | succ n ih =>
    intro E _ _ _ f hf hfc
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hasFDerivAt_translate_integral hf hfc hg x).differentiableAt,
      fun h => absurd h (by simp), ?_⟩
    have hfeq : fderiv ℝ (fun y : ℂ => ∫ θ in Ioc (0 : ℝ) (2 * π), f (y + g θ))
        = fun x => ∫ θ in Ioc (0 : ℝ) (2 * π), fderiv ℝ f (x + g θ) := by
      funext x
      exact (hasFDerivAt_translate_integral hf hfc hg x).fderiv
    rw [hfeq]
    have hfcs : HasCompactSupport (fderiv ℝ f) := HasCompactSupport.fderiv (𝕜 := ℝ) hfc
    exact ih (ℂ →L[ℝ] E) (fderiv ℝ f) (contDiff_infty_iff_fderiv.1 hf).2 hfcs

/-- **Smoothness of circle averages of test functions** (route (A)): `x ↦ ⨍_{∂B(x,R)} f` is a `C^∞` function. -/
theorem contDiff_circleAverage_of_contDiff {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (R : ℝ) : ContDiff ℝ ∞ (fun x : ℂ => Real.circleAverage f x R) := by
  have hcm : Continuous (fun θ : ℝ => circleMap 0 R θ) := continuous_circleMap 0 R
  have key : (fun x : ℂ => Real.circleAverage f x R)
      = fun x : ℂ => (2 * π)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * π), f (x + circleMap 0 R θ) := by
    funext x
    rw [Real.circleAverage, smul_eq_mul, intervalIntegral.integral_of_le (by positivity)]
    congr 2
    funext θ
    simp [circleMap]
  rw [key]
  have hT : ContDiff ℝ ∞ (fun x : ℂ => ∫ θ in Ioc (0 : ℝ) (2 * π), f (x + circleMap 0 R θ)) :=
    contDiff_infty.2 fun n => contDiff_translate_integral (fun θ : ℝ => circleMap 0 R θ) hcm n ℝ f hf hfc
  exact contDiff_const.mul hT

end HarmonicBalls

end
