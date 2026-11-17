import HarmonicBalls.Proofs.Sec9.ActualLQGSignedTestTransfer
import HarmonicBalls.Proofs.Potential.BoundedJensenPotentialIntegrability
import HarmonicBalls.Audit.GreenSubharmonicTestClass

/-! # Bounded signed Green tests for the LQG measure

A real-valued signed potential test and its compact-source representative have
identical center values and sub-mean inequalities under the actual LQG law.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace
open scoped ENNReal

/-- A bounded literal signed test transfers its sub-mean inequality to the
corresponding compact-source test, on one event for all admissible choices. -/
theorem IsWholePlaneGFF.ae_bounded_signed_test_subMeanValue
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (Λ O K : Set ℂ) (z : ℂ) (ν₁ ν₂ : Measure ℂ)
      (q f : ℂ → ℝ),
      IsOpen Λ → z ∈ Λ → IsOpen O → Bornology.IsBounded O → closure Λ ⊆ O →
      IsCompact K → K ⊆ O → IsFiniteMeasure ν₁ → IsFiniteMeasure ν₂ →
      ν₁ Kᶜ = 0 → ν₂ Kᶜ = 0 → ν₁ Λ = 0 → HarmonicOnNhd q O →
      (∀ x ∈ closure O, (∫⁻ y, greenKernelExtended O x y ∂ν₁) < ⊤ ∧
        (∫⁻ y, greenKernelExtended O x y ∂ν₂) < ⊤) →
      (∀ x ∈ closure O, f x = q x + ((∫⁻ y, greenKernelExtended O x y ∂ν₁).toReal -
        (∫⁻ y, greenKernelExtended O x y ∂ν₂).toReal)) →
      f z * (μ ω).real Λ ≤ ∫ x in Λ, f x ∂(μ ω) →
      (q + (greenPotential O ν₁ - greenPotential O ν₂)) ∈
          boundedSubharmonicBallTestClass Λ z ∧
      HasSubMeanValueProperty (μ ω) Λ z (q + (greenPotential O ν₁ - greenPotential O ν₂)) := by
  filter_upwards [hh.ae_singular_signed_greenPotential_integrable hγ hγ2 hαQ hμ, hμ] with ω hp hm
  let : IsLocallyFiniteMeasure (μ ω) := hm.isLocallyFiniteMeasure
  intro Λ O K z ν₁ ν₂ q f hΛ hz hO hOb hΛO hK hKO hf₁ hf₂ hν₁ hν₂ hνΛ hq hfinite hrep hineq
  have hΛb : Bornology.IsBounded Λ := hOb.subset (subset_closure.trans hΛO)
  have hcompact : IsCompact (closure Λ) := Metric.isCompact_of_isClosed_isBounded isClosed_closure hΛb.closure
  have hqint : IntegrableOn q Λ (μ ω) :=
    ((hq.continuousOn.mono hΛO).integrableOn_compact hcompact).mono_set subset_closure
  have hpot := hp O K K Λ ν₁ ν₂ hO hOb hK hK hν₁ hν₂ hf₁ hf₂ hΛb
  have hzO : z ∈ closure O := subset_closure (hΛO (subset_closure hz))
  have hcenter₁ := BoundedJensenFatou.greenPotential_eq_toReal_of_classical_lt_top hO hOb (hfinite z hzO).1
  have hcenter₂ := BoundedJensenFatou.greenPotential_eq_toReal_of_classical_lt_top hO hOb (hfinite z hzO).2
  have hcenter : (q + (greenPotential O ν₁ - greenPotential O ν₂)) z = f z := by
    rw [hrep z hzO]
    simp only [Pi.add_apply, Pi.sub_apply, hcenter₁.2.2, hcenter₂.2.2]
  have hae : (q + (greenPotential O ν₁ - greenPotential O ν₂)) =ᵐ[(μ ω).restrict Λ] f := by
    filter_upwards [hpot.2, ae_restrict_mem hΛ.measurableSet] with x hx hxΛ
    rw [hrep x (subset_closure (hΛO (subset_closure hxΛ)))]
    simp only [Pi.add_apply, Pi.sub_apply, hx.2.2.2.2.2.2]
  refine ⟨?_, ?_⟩
  · refine ⟨O, K, ν₁, ν₂, q, hO, hOb, hΛO, hK, hKO, hf₁, hf₂, hν₁, hν₂,
      hνΛ, hq, hcenter₂.1, hcenter₂.2.1, ?_⟩
    ext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  · refine ⟨hqint.add hpot.1, ?_⟩
    rw [hcenter, integral_congr_ae hae]
    exact hineq

end HarmonicBalls
