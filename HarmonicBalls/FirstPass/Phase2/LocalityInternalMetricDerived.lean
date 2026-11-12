import HarmonicBalls.FirstPass.Phase2.SupMeasurableDerived

/-!
# Internal metrics of the LQG metric on open sets are a.s. measurable (locality)

For the LQG metric `D_h` of `h = h^ℂ - α₀ log |·|` (`IsLQGMetricOfField`), the field axioms
`LQGMetricFieldAxiomsUnivFrozen` (Fact 2.2 I-IV) give: for every open set `W` and all `x, y ∈ ℂ`, the internal distance
`ω ↦ D_h(x, y; W)` is a.e.-measurable. For `x, y ∈ W` this is axiom II (locality): `D_h(x, y; W)` is a.s. equal to a
`σ(h|_W)`-measurable function, and `σ(h|_W)` is a sub-σ-algebra of the ambient one
(`IsWholePlaneGFF.fieldSigmaAlgebra_le`). If `x ∉ W` or `y ∉ W`, no path from `x` to `y` stays in `W` and the internal
distance is `∞`. In particular the local internal metrics `D_h(a, b; B(a, r) ∩ U)` of an open set `U`, which enter the
chain formula for the internal metric of a Weyl scaling `e^{ξ f} · D_h`, are a.s. measurable. The input
`LQGInternalMetricWeylAeMeasurableFrozen` is not used.

Also: for a continuous compactly supported `f`, the weight `ξ f` is uniformly continuous and bounded above.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

universe u

/-- **Derived from locality** (axiom II of `LQGMetricFieldAxiomsUnivFrozen`). For the γ-LQG metric `D_h` of
`h = h^ℂ - α₀ log |·|`, an open set `W` and any `x, y ∈ ℂ`, the internal distance `ω ↦ D_h(x, y; W)` is
a.e.-measurable. -/
theorem aemeasurable_internalMetric_of_fieldAxioms (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    {γ ξ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc) (hLQG : IsLQGMetricOfField P γ ξ α₀ hC D)
    {W : Set ℂ} (hWo : IsOpen W) (x y : ℂ) :
    AEMeasurable (fun ω => internalMetric (D ω) W x y) P := by
  by_cases hxy : x ∈ W ∧ y ∈ W
  · obtain ⟨𝔇, h𝔇, hD⟩ := hLQG
    have hax := hAx Ω P γ ξ α₀ hC hcirc hgff hγ0 hγ2 hα 𝔇 h𝔇
    have hDeq : ∀ᵐ ω ∂P, D ω = fun a b =>
        (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) a b).toReal := by
      filter_upwards [hD] with ω hDω
      funext a b
      obtain ⟨h0, h1⟩ := hDω a b
      rw [← h1, ENNReal.toReal_ofReal h0]
    obtain ⟨G, hGm, hGae⟩ := hax.2.1 W hWo
    refine ((hGm x y).mono (hgff.fieldSigmaAlgebra_le α₀ _) le_rfl).aemeasurable.congr ?_
    filter_upwards [hGae, hDeq] with ω hω hDω
    rw [hDω]
    exact (hω x hxy.1 y hxy.2).symm
  · have htop : ∀ ω, internalMetric (D ω) W x y = ⊤ := by
      intro ω
      unfold internalMetric
      refine iInf_eq_top.mpr fun p => iInf_eq_top.mpr fun hp => absurd ?_ hxy
      exact ⟨by simpa using hp 0, by simpa using hp 1⟩
    simp_rw [htop]
    exact aemeasurable_const

/-- For a continuous compactly supported `f`, the weight `z ↦ ξ f(z)` is uniformly continuous. -/
theorem uniformContinuous_const_mul_of_hasCompactSupport {f : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (ξ : ℝ) : UniformContinuous fun z => ξ * f z :=
  (hfc.mul_left (f := fun _ => ξ)).uniformContinuous_of_continuous (continuous_const.mul hf)

/-- For a continuous compactly supported `f`, the weight `z ↦ ξ f(z)` is bounded above. -/
theorem exists_const_mul_le_of_hasCompactSupport {f : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (ξ : ℝ) : ∃ K, ∀ z, ξ * f z ≤ K := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
  refine ⟨|ξ| * C, fun z => ?_⟩
  calc ξ * f z ≤ |ξ * f z| := le_abs_self _
    _ = |ξ| * |f z| := abs_mul _ _
    _ ≤ |ξ| * C := mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hC z) (abs_nonneg _)

end HarmonicBalls
