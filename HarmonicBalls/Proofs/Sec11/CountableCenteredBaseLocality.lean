import HarmonicBalls.Steps.Sec11.CountableCoordinateObservables
import HarmonicBalls.Proofs.Sec11.SingularMetricConstantShift

/-! # Normalized base metric on countably many endpoint pairs

The reference-centered field determines normalized internal base-metric
values on any countable family of endpoints. The Section 8 arguments imported
through the field-centering step use Leonardo Bonanno's LatticeProb code.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- Normalized internal base-metric distances at countably many local endpoint
pairs have a common modulo-constant measurable version, without assuming
samplewise linearity of GFF pairings. -/
theorem IsWholePlaneGFF.exists_modConst_countable_internal_baseMetric
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {U : Set ℂ} (hU : IsOpen U) (ψ : ℂ → ℝ)
    (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ U ∧ (p n).2 ∈ U) :
    ∃ (G : Ω → ℕ → ℝ≥0∞),
      Measurable[Section6.fieldSigmaAlgebraModConst α hC U] G ∧
      (∀ᵐ ω ∂P, ∀ n, internalMetric (fun x y => Real.exp (ξ * (-hC ω ψ)) * 𝔇 (hC ω) x y)
        U (p n).1 (p n).2 = G ω n) := by
  let c : Ω → ℝ := fun ω => -hC ω ψ
  have hc : Measurable c := (h.measurable_pairing ψ (hψ.mono_set (subset_univ _))).neg
  have ha := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun ω _ => c ω) h
    (fun _ => continuous_const) (fun _ => hc)
  obtain ⟨G, hG, hGeq⟩ := ha.locality U hU
  have hGmeas : Measurable[fieldSigmaAlgebra α
      (fun ω => addFunPairing (hC ω) (fun _ => -hC ω ψ)) U]
      (fun ω n => G ω (p n).1 (p n).2) := by
    rw [fieldSigmaAlgebra_eq, fieldSigmaAlgebra_eq_pairingSigmaAlgebra]
    have heq : (fun ω => fieldPairing 0
        (addFunPairing (hC ω) (fun _ => -hC ω ψ))) =
        (fun ω => addFunPairing (hC ω) (fun _ => c ω)) := by
      funext ω φ
      simp [fieldPairing, c]
    rw [heq]
    let : MeasurableSpace Ω := pairingSigmaAlgebra
      (fun ω => addFunPairing (hC ω) (fun _ => c ω)) U
    exact measurable_pi_iff.mpr (fun n => hG (p n).1 (p n).2)
  obtain ⟨H, hH, hHeq⟩ := h.exists_modConst_observable_of_reference_shift ψ hψ hψint
    (fun ω n => G ω (p n).1 (p n).2) hGmeas
  have hs := h.ae_baseMetric_add_random_constant 𝔇 h𝔇 c hc
  refine ⟨H, hH, ?_⟩
  filter_upwards [hs, hGeq, hHeq] with ω hs hg hh n
  have heq : 𝔇 (addFunPairing (hC ω) (fun _ => c ω)) =
      fun u v => Real.exp (ξ * c ω) * 𝔇 (hC ω) u v := by
    funext u v
    exact hs u v
  rw [← heq, hg (p n).1 (hp n).1 (p n).2 (hp n).2]
  exact (congrFun hh n).symm


end HarmonicBalls
