import HarmonicBalls.Steps.Sec11.ConeSingularWitness
import HarmonicBalls.Steps.Sec11.ConeOrdinaryUniform
import HarmonicBalls.Proofs.Sec6.CanonicalSingularMeasures

/-! # Uniform singular cone-event witnesses -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- For a given whole-plane realization, cofinal LQG measure existence and a
reference ordinary realization give a positive uniform inner probability for
all separated dyadic cone events. -/
theorem cone_singular_uniform_measurable_witness
    (hS : WholePlaneScaledBallMassStep.{u}) (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω Ω' : Type u} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} {μ' : Ω' → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc)
    (hG' : IsWholePlaneGFF P' hC' hcirc') (hE' : LQGMeasureExistence P' γ 0 hC' hcirc')
    (hμ' : IsLQGMeasureOfField P' γ 0 hcirc' μ')
    (Q : Set ℂ) (hQ : IsCone Q) {M : ℝ} (hM : 0 < M) :
    ∃ p : ℝ≥0∞, 0 < p ∧ ∀ (n : ℕ) (z : ℂ),
      dyadicScale n / 100 ≤ infDist (0 : ℂ) (annulus z (dyadicScale n) (6 * dyadicScale n)) →
      ∃ A ⊆ {ω | coneMassEvent (μ ω) Q M (dyadicScale n) z}, MeasurableSet A ∧ p ≤ P A := by
  let K : ℝ := ((1201 : ℝ) ^ |-(γ * α)|) ^ 2
  have hK : 0 < K := sq_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _)
  obtain ⟨p, hp, hpbound⟩ := cone_ordinary_event_uniform_positive hS hgrowth hγ hγ2 hG' hE' hμ'
    Q hQ (M := M * K) (mul_pos hM hK)
  obtain ⟨ν, hν, hrepr⟩ := Section6.exists_ae_all_subcritical_limits_eq_singularWeight_of_cofinal
    P γ hγ hγ2 hC hcirc hG hE
  have hweyl : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ := by
    filter_upwards [hrepr, hμ] with ω hω hm
    rw [hω α hα (μ ω) hm]
  refine ⟨p, hp, ?_⟩
  intro n z hd
  obtain ⟨A, hA, hAm, hAbound⟩ := exists_cone_measurable_subset_of_singular_weight
    P (dyadicScale_pos n) hM.le hQ hd (hG.aemeasurable_lqgMeasure hμ) hweyl
  exact ⟨A, hA, hAm, (hpbound P hC hcirc ν hG hν n z).trans hAbound⟩

end HarmonicBalls

#print axioms HarmonicBalls.cone_singular_uniform_measurable_witness
