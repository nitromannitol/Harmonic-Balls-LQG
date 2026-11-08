import Mathlib

/-! # Route (A), C3 (random part): integrability for the L²-Fubini identity

For a jointly measurable field `Z : Ω × ℂ → ℝ` with continuous sample paths `z ↦ Z ω z` and a uniform second-moment
bound `∫ Z(·, z)² dP ≤ C` on a compact `K`, and a continuous `ψ` supported in `K`, the weighted square
`(ω, z) ↦ |ψ(z)| Z(ω, z)²` is integrable on `P ⊗ dz`. This is the input of the Fubini identity
`E[(∫ Z(·,z) ψ(z) dz)²] = ∫∫ ψ(z) ψ(z') E[Z(·,z) Z(·,z')] dz dz'` used in the Gaussian covariance argument of
C3 (route (A) of r8, "first in L² from the joint Gaussian covariance formula").
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- Integrability of `(ω, z) ↦ |ψ z| Z(ω, z)²` on `P ⊗ volume` (Tonelli for the second moments). -/
theorem integrable_abs_mul_sq_prod {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℂ → ℝ}
    (hZm : Measurable (fun p : Ω × ℂ => Z p.1 p.2)) (hcont : ∀ ω, Continuous (Z ω))
    {K : Set ℂ} (hK : IsCompact K) {ψ : ℂ → ℝ} (hψc : Continuous ψ) (hψK : ∀ z, z ∉ K → ψ z = 0)
    {C : ℝ≥0∞} (hCt : C < ⊤) (hL2 : ∀ z ∈ K, ∫⁻ ω, ENNReal.ofReal (Z ω z ^ 2) ∂P ≤ C) :
    Integrable (fun q : Ω × ℂ => |ψ q.2| * Z q.1 q.2 ^ 2) (P.prod volume) := by
  have hmeas : Measurable (fun q : Ω × ℂ => |ψ q.2| * Z q.1 q.2 ^ 2) :=
    ((continuous_abs.measurable.comp (hψc.measurable.comp measurable_snd))).mul (hZm.pow_const 2)
  -- the pointwise bound `∫⁻ ω, ofReal(|ψ y| Z(ω,y)²) ≤ |ψ y| C` for every `y`
  have hbound : ∀ y : ℂ, ∫⁻ ω, ENNReal.ofReal (|ψ y| * Z ω y ^ 2) ∂P ≤ ENNReal.ofReal |ψ y| * C := by
    intro y
    by_cases hy : y ∈ K
    · calc ∫⁻ ω, ENNReal.ofReal (|ψ y| * Z ω y ^ 2) ∂P
          = ∫⁻ ω, ENNReal.ofReal |ψ y| * ENNReal.ofReal (Z ω y ^ 2) ∂P := by
            refine lintegral_congr fun ω => ?_
            rw [ENNReal.ofReal_mul (abs_nonneg _)]
        _ = ENNReal.ofReal |ψ y| * ∫⁻ ω, ENNReal.ofReal (Z ω y ^ 2) ∂P :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal |ψ y| * C := by
            gcongr
            exact hL2 y hy
    · have h0 : ψ y = 0 := hψK y hy
      simp [h0]
  have hsec : ∀ ω, Integrable (fun y => |ψ y| * Z ω y ^ 2) (volume : Measure ℂ) := by
    intro ω
    have hcs : Continuous (fun y => |ψ y| * Z ω y ^ 2) :=
      (continuous_abs.comp hψc).mul ((hcont ω).pow 2)
    exact hcs.integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK (fun y hy => by simp [hψK y hy]))
  have hpos : ∀ (ω : Ω) (y : ℂ), ‖|ψ y| * Z ω y ^ 2‖ = |ψ y| * Z ω y ^ 2 := fun ω y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hg : Integrable (fun ω => ∫ y, ‖|ψ y| * Z ω y ^ 2‖ ∂(volume : Measure ℂ)) P := by
    refine ⟨(hmeas.norm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have hnn : ∀ ω, 0 ≤ ∫ y, ‖|ψ y| * Z ω y ^ 2‖ ∂(volume : Measure ℂ) := fun ω =>
      integral_nonneg fun y => norm_nonneg _
    calc ∫⁻ ω, ‖∫ y, ‖|ψ y| * Z ω y ^ 2‖ ∂(volume : Measure ℂ)‖ₑ ∂P
        = ∫⁻ ω, ENNReal.ofReal (∫ y, ‖|ψ y| * Z ω y ^ 2‖ ∂(volume : Measure ℂ)) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn ω)]
      _ = ∫⁻ ω, ∫⁻ y, ENNReal.ofReal ‖|ψ y| * Z ω y ^ 2‖ ∂(volume : Measure ℂ) ∂P := by
          refine lintegral_congr fun ω => ?_
          exact ofReal_integral_eq_lintegral_ofReal (hsec ω).norm (ae_of_all _ fun y => norm_nonneg _)
      _ = ∫⁻ y, ∫⁻ ω, ENNReal.ofReal ‖|ψ y| * Z ω y ^ 2‖ ∂P ∂(volume : Measure ℂ) := by
          refine lintegral_lintegral_swap ?_
          exact (hmeas.norm.ennreal_ofReal).aemeasurable
      _ ≤ ∫⁻ y, ENNReal.ofReal |ψ y| * C ∂(volume : Measure ℂ) := by
          refine lintegral_mono fun y => ?_
          simpa only [hpos] using hbound y
      _ = (∫⁻ y, ENNReal.ofReal |ψ y| ∂(volume : Measure ℂ)) * C :=
          lintegral_mul_const' _ _ hCt.ne
      _ < ⊤ := by
          refine ENNReal.mul_lt_top ?_ hCt
          exact (hψc.abs.integrable_of_hasCompactSupport
            (HasCompactSupport.intro hK (fun y hy => by simp [hψK y hy]))).lintegral_lt_top
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  exact ⟨ae_of_all _ hsec, hg⟩

end HarmonicBalls

end
