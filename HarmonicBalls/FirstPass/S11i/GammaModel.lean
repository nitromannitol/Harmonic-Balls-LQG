import HarmonicBalls.FirstPass.S11r
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.Defs.LQGMetric

/-!
# Insertion-`γ` model on the realization of an insertion-`α₀` model (fp-S11i, owner n3)

This file discharges the hypothesis `hγM` of `correctedLemma11_13_of_gamma_identity` (`FirstPass/S11i/Assembly13.lean`).
Given a whole-plane model `(μ, D)` at `(γ, ξ, α₀)` on a realization `(Ω, P, hC, hcirc)`, the same realization carries a
whole-plane model at `(γ, ξ, γ)` with the SAME exponent `ξ`. The insertion-`γ` measure exists by `LQGMeasureExistence` at
`α₀ = γ`; the insertion-`γ` metric is the Weyl scaling at `γ` of the root metric `𝔇` of the given model (`IsLQGMetricOfField`
supplies `IsLQGMetric γ ξ 𝔇`), finite almost surely by `LQGMetricFieldAxioms` (item I). The inputs are those of
`hmodel_at_gamma` (`FirstPass/S11r.lean`). That lemma chooses some exponent, which need not be the given `ξ`; this one does not.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

namespace FirstPassS11iGamma

/-- **Insertion-`γ` model on a given realization.** For `γ ∈ (0, 2)` and a whole-plane GFF realization carrying a model at
`(γ, ξ, α₀)` (with `α₀ < Q_γ`), the same realization carries a model at `(γ, ξ, γ)`: an LQG measure at insertion `γ` and an
LQG metric of exponent `ξ` at insertion `γ` whose root is the root `𝔇` of the given metric. -/
theorem gammaModel_of_alpha0Model
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hMeas : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ γ hC hcirc)
    {γ ξ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc) (D₀ : Ω → ℂ → ℂ → ℝ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D₀) :
    ∃ (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsLQGMeasureOfField P γ γ hcirc μ ∧ IsLQGMetricOfField P γ ξ γ hC D := by
  obtain ⟨𝔇, h𝔇, -⟩ := hD
  have hQ : γ < lqgQ γ := lt_lqgQ_of_mem_Ioo hγ0 hγ2
  obtain ⟨μ, hμ⟩ := hMeas γ Ω P hC hcirc hG hγ0 hγ2 hQ
  have hI := (hAx γ ξ γ Ω P hC hcirc hG hγ0 hγ2 hQ 𝔇 h𝔇).1
  refine ⟨μ, fun ω u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -γ * Real.log ‖x‖) u v).toReal, hμ, ⟨𝔇, h𝔇, ?_⟩⟩
  filter_upwards [hI] with ω hω
  intro u v
  exact ⟨ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (ne_top_of_lt (hω.1 u v))⟩

end FirstPassS11iGamma

end HarmonicBalls

#print axioms HarmonicBalls.FirstPassS11iGamma.gammaModel_of_alpha0Model
