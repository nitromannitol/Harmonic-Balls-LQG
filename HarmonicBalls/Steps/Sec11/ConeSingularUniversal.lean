import HarmonicBalls.Steps.Sec11.ConeSingularUniform

/-! # Universal singular cone-event witnesses -/

namespace HarmonicBalls

/-! The cone-probability development uses Leonardo Bonanno's
Lattice-Probability formalization, including its Cameron-Martin port through
the local smooth-shift and fixed-shift decoder developments. -/

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- A reference realization fixes one positive probability for all singular
realizations satisfying the cofinal measure-existence input. -/
theorem cone_singular_universal_measurable_witness
    (hS : WholePlaneScaledBallMassStep.{u}) (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω' : Type u} [MeasurableSpace Ω'] {P' : Measure Ω'} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} {μ' : Ω' → Measure ℂ}
    (hG' : IsWholePlaneGFF P' hC' hcirc') (hE' : LQGMeasureExistence P' γ 0 hC' hcirc')
    (hμ' : IsLQGMeasureOfField P' γ 0 hcirc' μ')
    (Q : Set ℂ) (hQ : IsCone Q) {M : ℝ} (hM : 0 < M) :
    ∃ p : ℝ≥0∞, 0 < p ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      (∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) →
      ∀ (n : ℕ) (z : ℂ),
      dyadicScale n / 100 ≤ infDist (0 : ℂ) (annulus z (dyadicScale n) (6 * dyadicScale n)) →
      ∃ A ⊆ {ω | coneMassEvent (μ ω) Q M (dyadicScale n) z}, MeasurableSet A ∧ p ≤ P A := by
  let K : ℝ := ((1201 : ℝ) ^ |-(γ * α)|) ^ 2
  have hK : 0 < K := sq_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨P' {ω | coneMassEvent (μ' ω) Q (M * K) 1 0}, ?_, ?_⟩
  · exact cone_unit_event_positive hS hgrowth hγ hγ2 (by unfold lqgQ; positivity)
      hG' hE' hμ' Q hQ (mul_pos hM hK)
  · intro Ω _ P hC hcirc μ hG hμ hE n z hd
    obtain ⟨ν, hν, hrepr⟩ := Section6.exists_ae_all_subcritical_limits_eq_singularWeight_of_cofinal
      P γ hγ hγ2 hC hcirc hG hE
    have hweyl : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
        ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ := by
      filter_upwards [hrepr, hμ] with ω hω hm
      rw [hω α hα (μ ω) hm]
    obtain ⟨A, hA, hAm, hAbound⟩ := exists_cone_measurable_subset_of_singular_weight
      P (dyadicScale_pos n) hM.le hQ hd (hG.aemeasurable_lqgMeasure hμ) hweyl
    refine ⟨A, hA, hAm, ?_⟩
    rw [← cone_ordinary_event_probability_eq_reference hγ hG hG' hν hμ' Q hQ (M * K) n z]
    exact hAbound

end HarmonicBalls
