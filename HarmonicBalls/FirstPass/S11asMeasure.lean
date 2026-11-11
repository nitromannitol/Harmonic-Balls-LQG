import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.Defs.LQGMetric

/-!
# Measure half of the rooted local rescaling: observation identity and local proportionality

Block 1 (deterministic): a smooth shift `f` that equals the background `-α₀ log‖·‖` on the disc `D` does not change the
rooted mean-zero observation on `D` when the background is moved from `α₀` to `0`.

Block 2 (from the frozen common local decoder, `LocalLQGDecoderCommonFrozen` clause 2): two rooted LQG measures whose
rooted mean-zero observations on the disc `D` coincide are, almost surely, proportional on `D`. The second model is taken
under a measure `P'` with `P ≪ P'`, so that the almost sure statement transfers back to `P` (Cameron–Martin reweighting).

Named inputs (hypotheses, not proved here): `LocalLQGDecoderCommonFrozen` (FIRST-PASS FROZEN).
-/

namespace FirstPassS11asMeasure

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls

universe u

/-- **Block 1: observation identity under a background-absorbing shift.** If `f = -α₀ log‖·‖` on `D`, then the rooted
mean-zero observation of the field `h - α₀ log|·|` (root `z`, insertion `γ`) on `D` equals the rooted observation with
background `0` of the shifted field `h + f`. Only test functions supported in `D` are seen. -/
theorem rootedMeanZeroObs_eq_addFun {α₀ γ : ℝ} {D : Set ℂ} {z : ℂ} {hC : (ℂ → ℝ) → ℝ} {f : ℂ → ℝ}
    (hf : ∀ x ∈ D, f x = -α₀ * Real.log ‖x‖)
    (φ : {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0}) :
    rootedMeanZeroObs α₀ γ D z hC φ = rootedMeanZeroObs 0 γ D z (addFunPairing hC f) φ := by
  have hsupp : ∀ x, x ∉ D → φ.1 x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (φ.2.1.2.2 h))
  have hint : ∫ x, f x * φ.1 x = -α₀ * ∫ x, φ.1 x * Real.log ‖x‖ := by
    rw [← integral_const_mul]
    congr 1
    funext x
    by_cases hx : x ∈ D
    · rw [hf x hx]
      ring
    · rw [hsupp x hx]
      simp
  simp only [rootedMeanZeroObs, fieldPairing, addFunPairing, zero_mul, sub_zero]
  rw [hint]
  ring

/-- **Block 2: local proportionality of rooted LQG measures from the common decoder.** Let `K` be the common local decoder
on the disc `D = ball c₂ r₂` (`LocalLQGDecoderCommonFrozen`, clause 2). If the rooted observations of two models at the
same root `z` coincide on `D`, then almost surely the two rooted LQG measures are proportional on `D`, in the sense
`c₀ • μ₀|_D = c₁ • μ₁|_D` with `0 < c₀, c₁ < ∞`. The second model is under `P'` with `P ≪ P'`. -/
theorem rootedMeasure_restrict_proportional (hK : LocalLQGDecoderCommonFrozen.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P P' : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {c₂ : ℂ} {r₂ : ℝ} (hr₂ : 0 < r₂) (h0 : (0 : ℂ) ∉ closedBall c₂ r₂)
    {α₀ α₁ : ℝ} (hα₀ : α₀ < lqgQ γ) (hα₁ : α₁ < lqgQ γ) {z : ℂ}
    {hC₀ hC₁ : Ω → (ℂ → ℝ) → ℝ} {hc₀ hc₁ : Ω → ℝ → ℂ → ℝ} {μ₀ μ₁ : Ω → Measure ℂ}
    (hW₀ : IsWholePlaneGFF P hC₀ hc₀) (hW₁ : IsWholePlaneGFF P' hC₁ hc₁)
    (hμ₀ : IsLQGMeasure P γ (fun ω => rootedCircleAverage α₀ γ z (hc₀ ω)) μ₀)
    (hμ₁ : IsLQGMeasure P' γ (fun ω => rootedCircleAverage α₁ γ z (hc₁ ω)) μ₁)
    (hPP : P ≪ P')
    (hobs : ∀ ω, rootedMeanZeroObs α₀ γ (ball c₂ r₂) z (hC₀ ω) = rootedMeanZeroObs α₁ γ (ball c₂ r₂) z (hC₁ ω)) :
    ∀ᵐ ω ∂P, ∃ c₀ c₁ : ℝ≥0∞, 0 < c₀ ∧ c₀ < ⊤ ∧ 0 < c₁ ∧ c₁ < ⊤ ∧
      c₀ • (μ₀ ω).restrict (ball c₂ r₂) = c₁ • (μ₁ ω).restrict (ball c₂ r₂) := by
  obtain ⟨K, -, -, hcl2⟩ := hK γ hγ0 hγ2 c₂ r₂ hr₂ h0
  have h0' := hcl2 α₀ hα₀ z Ω P hC₀ hc₀ μ₀ hW₀ hμ₀
  have h1' := hcl2 α₁ hα₁ z Ω P' hC₁ hc₁ μ₁ hW₁ hμ₁
  have h1 : ∀ᵐ ω ∂P, _ := hPP.ae_le h1'
  filter_upwards [h0', h1] with ω hω0 hω1
  obtain ⟨c₀, hc₀pos, hc₀top, hK0⟩ := hω0
  obtain ⟨c₁, hc₁pos, hc₁top, hK1⟩ := hω1
  rw [hobs ω] at hK0
  exact ⟨c₀, c₁, hc₀pos, hc₀top, hc₁pos, hc₁top, hK0.symm.trans hK1⟩

end FirstPassS11asMeasure
