import HarmonicBalls.FirstPass.Phase2.LQGGraphDimensionUnique
import HarmonicBalls.FirstPass.Phase2.HModelAtGammaDerived
import HarmonicBalls.FirstPass.S11i.Faithful
import HarmonicBalls.Proofs.GFF.LQGMetricExistence

/-!
# The canonical Weyl exponent `ξ = γ / d_γ`

The paper's canonical exponent is `lqgXi γ = γ / lqgGraphDimension γ` (`FirstPass/S11i/Faithful.lean`), while the
LQG metric constructed in `Proofs/GFF/LQGMetricExistence.lean` has Weyl exponent `LQGMetric.xiGamma γ =
γ / LQGMetric.dGamma γ` (Gwynne-Miller, arXiv:1905.00383, equation (1.1)), where `LQGMetric.dGamma γ = 2 / χ` with
`χ` the Liouville graph-distance exponent of Ding-Zeitouni-Zhang (Theorem 1.1).

* `hmodel_at_gamma_xiGamma`: a whole-plane GFF realization in `Type` with its LQG measure and an LQG metric of
  Weyl exponent `LQGMetric.xiGamma γ` at insertion `γ`, with no input.
* `lqgXi_eq_xiGamma_of_isWholePlaneLQGDimension`: as soon as `LQGMetric.dGamma γ` characterizes the whole-plane
  graph-distance dimension (Ding-Gwynne, arXiv:1807.01072v3, Theorem 1.4), the two exponents agree; hence the
  canonical realization exists at `ξ = lqgXi γ`.
-/

namespace HarmonicBalls

open MeasureTheory

/-- **Realization at `(γ, LQGMetric.xiGamma γ, γ)`, no inputs.** For `γ ∈ (0, 2)` some probability space in `Type`
carries a normalized whole-plane GFF, its LQG measure at insertion `γ`, and an LQG metric of Weyl exponent
`LQGMetric.xiGamma γ` at insertion `γ`. -/
theorem hmodel_at_gamma_xiGamma {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (hC₀ : Ω₀ → (ℂ → ℝ) → ℝ) (hcirc₀ : Ω₀ → ℝ → ℂ → ℝ) (μ₀ : Ω₀ → Measure ℂ) (D₀ : Ω₀ → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P₀ hC₀ hcirc₀ ∧ IsLQGMeasureOfField P₀ γ γ hcirc₀ μ₀ ∧
        IsLQGMetricOfField P₀ γ (LQGMetric.xiGamma γ) γ hC₀ D₀ := by
  obtain ⟨-, 𝔇, h𝔇⟩ := exists_isLQGMetric hγ0 hγ2
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, hC₀, hcirc₀, hGFF₀⟩ := wholePlaneGFFExistsFrozen_derived'.{0}
  have hQ : γ < lqgQ γ := lt_lqgQ_of_mem_Ioo hγ0 hγ2
  obtain ⟨μ₀, hμ₀⟩ := lqgMeasureExistence_derived P₀ γ γ hC₀ hcirc₀ hGFF₀ hγ0 hγ2 hQ
  have hI := (lqgMetricFieldAxiomsUnivFrozen_derived.{0} Ω₀ P₀ γ (LQGMetric.xiGamma γ) γ hC₀ hcirc₀ hGFF₀
    hγ0 hγ2 hQ 𝔇 h𝔇).1
  refine ⟨Ω₀, mΩ₀, P₀, hP₀, hC₀, hcirc₀, μ₀,
    fun ω u v => (weylScaling (𝔇 (hC₀ ω)) (LQGMetric.xiGamma γ) (fun x => -γ * Real.log ‖x‖) u v).toReal,
    hGFF₀, hμ₀, ?_⟩
  unfold IsLQGMetricOfField
  refine ⟨𝔇, h𝔇, ?_⟩
  filter_upwards [hI] with ω hω
  intro u v
  exact ⟨ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (ne_top_of_lt (hω.1 u v))⟩

/-- **The canonical exponent is Gwynne-Miller's.** If `LQGMetric.dGamma γ` characterizes the whole-plane Liouville
graph-distance dimension, then `lqgXi γ = LQGMetric.xiGamma γ`. -/
theorem lqgXi_eq_xiGamma_of_isWholePlaneLQGDimension {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (h : IsWholePlaneLQGDimension γ (LQGMetric.dGamma γ)) : lqgXi γ = LQGMetric.xiGamma γ := by
  show γ / lqgGraphDimension γ = γ / LQGMetric.dGamma γ
  rw [lqgGraphDimension_eq_of_isWholePlaneLQGDimension hγ0 hγ2 h]

/-- **Canonical realization.** If `LQGMetric.dGamma γ` characterizes the whole-plane graph-distance dimension, a
whole-plane GFF realization in `Type` carries an LQG metric of the canonical Weyl exponent `lqgXi γ`. -/
theorem hmodel_at_gamma_lqgXi_of_isWholePlaneLQGDimension {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (h : IsWholePlaneLQGDimension γ (LQGMetric.dGamma γ)) :
    ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (hC₀ : Ω₀ → (ℂ → ℝ) → ℝ) (hcirc₀ : Ω₀ → ℝ → ℂ → ℝ) (μ₀ : Ω₀ → Measure ℂ) (D₀ : Ω₀ → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P₀ hC₀ hcirc₀ ∧ IsLQGMeasureOfField P₀ γ γ hcirc₀ μ₀ ∧
        IsLQGMetricOfField P₀ γ (lqgXi γ) γ hC₀ D₀ := by
  rw [lqgXi_eq_xiGamma_of_isWholePlaneLQGDimension hγ0 hγ2 h]
  exact hmodel_at_gamma_xiGamma hγ0 hγ2

end HarmonicBalls
