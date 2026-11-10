import HarmonicBalls.FirstPass.S11u.Mixed

/-!
# Variance of a pairing minus a circle average, and a.s. convergence from summable second moments (fp-S11u, owner n4)

For a whole-plane GFF `(P, hC, hcirc)` and a test function `φ`, the variance of `hC φ - hcirc(r, z)` is the
combination `Kpp + Kzz - 2 Kpc` of the three kernel integrals (`IsWholePlaneGFF.covariance_eq`, `wholePlaneGFFCov`).
A centered random variable has variance equal to its second moment; summable second moments give almost sure
convergence (the lintegral-of-series argument).
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal

universe u

/-- The variance of `hC φ - hcirc(r, z)` is the whole-plane kernel combination. -/
theorem variance_pairing_sub_circle_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (φ : ℂ → ℝ) (hφ : IsTestFunction univ φ) :
    variance (fun ω => hC ω φ - hcirc ω r z) P =
      (∫ x, φ x * ∫ y, φ y * wholePlaneCov x y) +
        Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) z r) z r -
      2 * ∫ x, φ x * Real.circleAverage (fun y => wholePlaneCov x y) z r := by
  have := hGFF.isProbabilityMeasure
  have hp : MemLp (fun ω => hC ω φ) 2 P :=
    (hGFF.isGaussianProcess.hasGaussianLaw_eval
      (⟨.pairing φ, hφ⟩ : GFFObservable.Admissible)).memLp (by simp)
  have hz : MemLp (fun ω => hcirc ω r z) 2 P := (hGFF.hasGaussianLaw_circle hr z).memLp (by simp)
  change variance ((fun ω => hC ω φ) - (fun ω => hcirc ω r z)) P = _
  rw [variance_sub hp hz, ← covariance_self hp.aemeasurable, ← covariance_self hz.aemeasurable]
  have hpp := hGFF.covariance_eq (.pairing φ) (.pairing φ) hφ hφ
  have hzz := hGFF.covariance_eq (.circle r z) (.circle r z) hr hr
  have hpz := hGFF.covariance_eq (.pairing φ) (.circle r z) hφ hr
  simp only [GFFObservable.eval] at hpp hzz hpz
  rw [hpp, hzz, hpz]
  have key : ∀ a b c : ℝ, a - 2 * c + b = a + b - 2 * c := fun a b c => by ring
  rw [key]
  rfl

/-- A centered `hC φ - hcirc(r, z)` has variance equal to its second moment. -/
theorem integral_sq_pairing_sub_circle_eq_variance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (φ : ℂ → ℝ) (hφ : IsTestFunction univ φ) :
    ∫ ω, (hC ω φ - hcirc ω r z) ^ 2 ∂P = variance (fun ω => hC ω φ - hcirc ω r z) P := by
  have := hGFF.isProbabilityMeasure
  have hp : MemLp (fun ω => hC ω φ) 2 P :=
    (hGFF.isGaussianProcess.hasGaussianLaw_eval
      (⟨.pairing φ, hφ⟩ : GFFObservable.Admissible)).memLp (by simp)
  have hz : MemLp (fun ω => hcirc ω r z) 2 P := (hGFF.hasGaussianLaw_circle hr z).memLp (by simp)
  have hD : MemLp (fun ω => hC ω φ - hcirc ω r z) 2 P := hp.sub hz
  have hmean : ∫ ω, (hC ω φ - hcirc ω r z) ∂P = 0 := by
    have h1 := hGFF.integral_eq_zero (.pairing φ) hφ
    have h2 := hGFF.integral_eq_zero (.circle r z) hr
    simp only [GFFObservable.eval] at h1 h2
    rw [integral_sub (hp.integrable (by norm_num)) (hz.integrable (by norm_num)), h1, h2, sub_zero]
  rw [variance_eq_sub hD]
  simp only [Pi.pow_apply, hmean, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]

/-- Summable second moments give almost sure convergence to zero. -/
theorem ae_tendsto_zero_of_summable_integral_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (D : ℕ → Ω → ℝ) (hD : ∀ j, MemLp (D j) 2 P) (b : ℕ → ℝ)
    (hb : Summable b) (hbound : ∀ j, ∫ ω, (D j ω) ^ 2 ∂P ≤ b j) :
    ∀ᵐ ω ∂P, Tendsto (fun j => D j ω) atTop (𝓝 0) := by
  have hsq : ∀ j, Integrable (fun ω => (D j ω) ^ 2) P := fun j => (hD j).integrable_sq
  have hnn : ∀ j, 0 ≤ᵐ[P] fun ω => (D j ω) ^ 2 := fun j => Filter.Eventually.of_forall fun ω => sq_nonneg _
  have hbnn : ∀ j, 0 ≤ b j := fun j => (integral_nonneg fun ω => sq_nonneg _).trans (hbound j)
  have hmeas : ∀ j, AEMeasurable (fun ω => ENNReal.ofReal ((D j ω) ^ 2)) P := fun j =>
    ((hD j).aemeasurable.pow_const 2).ennreal_ofReal
  have hFm : AEMeasurable (fun ω => ∑' j, ENNReal.ofReal ((D j ω) ^ 2)) P :=
    AEMeasurable.tsum hmeas
  have hlint : ∫⁻ ω, ∑' j, ENNReal.ofReal ((D j ω) ^ 2) ∂P ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    have heq : ∀ j, ∫⁻ ω, ENNReal.ofReal ((D j ω) ^ 2) ∂P = ENNReal.ofReal (∫ ω, (D j ω) ^ 2 ∂P) :=
      fun j => (ofReal_integral_eq_lintegral_ofReal (hsq j) (hnn j)).symm
    simp only [heq]
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal (hbound j)) ?_)
    rw [← ENNReal.ofReal_tsum_of_nonneg hbnn hb]
    exact ENNReal.ofReal_lt_top
  filter_upwards [ae_lt_top' hFm hlint] with ω hω
  have hsum : Summable (fun j => (D j ω) ^ 2) := by
    have h := ENNReal.summable_toReal (f := fun j => ENNReal.ofReal ((D j ω) ^ 2)) hω.ne
    exact h.congr fun j => ENNReal.toReal_ofReal (sq_nonneg _)
  have h2 : Tendsto (fun j => (D j ω) ^ 2) atTop (𝓝 0) := hsum.tendsto_atTop_zero
  have h3 : Tendsto (fun j => |D j ω|) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp h2
    have hfun : (fun j => |D j ω|) = fun j => √((D j ω) ^ 2) := funext fun j => (Real.sqrt_sq_eq_abs _).symm
    rw [hfun]
    simpa [Function.comp_def, Real.sqrt_zero] using h
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr h3

end HarmonicBalls
