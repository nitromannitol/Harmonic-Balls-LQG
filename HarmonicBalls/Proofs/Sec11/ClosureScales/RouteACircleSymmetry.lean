import Mathlib

/-! # Route (A), C3 (deterministic core): symmetry of the circle-average kernel

For continuous compactly supported `F, ψ : ℂ → ℝ` and `R : ℝ`, the integral of `ψ` against the circle averages of `F`
equals the integral of `F` against the circle averages of `ψ`:
`∫ z, ψ z * ⨍_{∂B(z,R)} F = ∫ x, F x * ⨍_{∂B(x,-R)} ψ`  (`Real.circleAverage`).
This is Fubini in the variables `(z, θ)` and `(x, θ)`, with the translation `z ↦ z + circleMap 0 R θ`.
The identity underlies the identification of `∫ hcirc(r, z) ψ(z) dz` with the pairing of the smoothed test function.
-/

noncomputable section

open MeasureTheory Set Metric Complex
open scoped ENNReal

namespace HarmonicBalls

/-- Integrability of a continuous function on `ℂ × ℝ` that vanishes off `K × ℝ` (`K` compact), against the product of
Lebesgue measure on `ℂ` and of Lebesgue measure restricted to `Icc a b`. -/
theorem integrable_prod_volume_restrict_Icc {K : Set ℂ} (hK : IsCompact K) {a b : ℝ}
    {g : ℂ × ℝ → ℝ} (hg : Continuous g) (hgK : ∀ p : ℂ × ℝ, p.1 ∉ K → g p = 0) :
    Integrable g ((volume : Measure ℂ).prod (volume.restrict (Icc a b))) := by
  set S : Set (ℂ × ℝ) := K ×ˢ Icc a b with hSdef
  set T : Set (ℂ × ℝ) := univ ×ˢ Icc a b with hTdef
  have hS : IsCompact S := hK.prod isCompact_Icc
  have hSm : MeasurableSet S := hS.measurableSet
  have hTm : MeasurableSet T := MeasurableSet.univ.prod measurableSet_Icc
  have h1 : IntegrableOn g S ((volume : Measure ℂ).prod (volume : Measure ℝ)) :=
    hg.continuousOn.integrableOn_compact hS
  have hfun : T.indicator g = S.indicator g := by
    funext p
    by_cases hp : p ∈ S
    · have hpT : p ∈ T := ⟨mem_univ _, hp.2⟩
      rw [indicator_of_mem hp, indicator_of_mem hpT]
    · rw [indicator_of_notMem hp]
      by_cases hpT : p ∈ T
      · rw [indicator_of_mem hpT]
        exact hgK p (fun hpK => hp ⟨hpK, hpT.2⟩)
      · rw [indicator_of_notMem hpT]
  have hT : IntegrableOn g T ((volume : Measure ℂ).prod (volume : Measure ℝ)) := by
    rw [← integrable_indicator_iff hTm, hfun, integrable_indicator_iff hSm]
    exact h1
  have hμ : (volume : Measure ℂ).prod (volume.restrict (Icc a b))
      = ((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict T := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hμ]
  exact hT

end HarmonicBalls

end
