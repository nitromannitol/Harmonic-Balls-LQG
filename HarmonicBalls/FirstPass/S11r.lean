import HarmonicBalls.Defs.Notation
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.FirstPass.S11r.Frozen

/-!
# Realization of the LQG model at insertion `γ`

Lemma `hmodel_at_gamma` is the model hypothesis `hmodel` of `certificate_canonical_pos` (FirstPass/S11i/CertificateCanonical.lean,
B3): for `γ ∈ (0, 2)` there are an exponent `ξ > 0` and one whole-plane GFF realization `(Ω₀, P₀, hC₀, hcirc₀)` with an
LQG measure `μ₀` and an LQG metric `D₀` at insertion `α₀ = γ`. The statement is the same expression as `hmodel` with `ξ` existential.

Inputs (all hypotheses, none derived here):
- `WholePlaneGFFExistsFrozen.{u}` (FirstPass/S11r/Frozen.lean): existence of a whole-plane GFF (EXTERNAL, general).
- `hMeas`: `LQGMeasureExistence` (Proposed/LQG.lean:66) at `α₀ = γ`, for every realization `Ω : Type u` (universal closure of the
  Proposed Prop over the probability space, as in FirstPass/S11b.lean:73).
- `LQGMetricExistenceUniqueness` (Proposed/LQG.lean:173): the exponent `ξ > 0` and a metric `𝔇` with `IsLQGMetric γ ξ 𝔇`.
- `LQGMetricFieldAxiomsUnivFrozen.{u}` (FirstPass/Frozen/S11j.lean): Fact 2.2 (Proposed/LQG.lean:199) in universe `u`. Item I gives
  a.s. finiteness of the Weyl-scaled metric at the insertion, so the real-valued `D₀` below represents it exactly.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- The insertion condition `α₀ < Q_γ` at `α₀ = γ`, for `γ ∈ (0, 2)`: `γ < 2/γ + γ/2` since `γ² < 4`. -/
theorem lt_lqgQ_of_mem_Ioo {γ : ℝ} (h0 : 0 < γ) (h2 : γ < 2) : γ < lqgQ γ := by
  unfold lqgQ
  have h : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) h0]
    nlinarith
  linarith

/-- **Realization at `(γ, ξ, γ)`** (the model `hmodel` of `certificate_canonical_pos`, with `ξ` existential): for `γ ∈ (0, 2)`
there are `ξ > 0` and a whole-plane GFF realization with an LQG measure and an LQG metric of Weyl exponent `ξ` at insertion `γ`.
The metric is `D₀ ω u v = (weylScaling (𝔇 (hC₀ ω)) ξ (-γ log|·|) u v).toReal`, which equals the field-level metric of
`IsLQGMetricOfField` a.s. because that metric is finite (Fact 2.2 I, `LQGMetricFieldAxioms`). -/
theorem hmodel_at_gamma (hGFF : WholePlaneGFFExistsFrozen.{u})
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hMeas : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ γ hC hcirc)
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) (hMet : LQGMetricExistenceUniqueness) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ (Ω₀ : Type u) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (hC₀ : Ω₀ → (ℂ → ℝ) → ℝ) (hcirc₀ : Ω₀ → ℝ → ℂ → ℝ) (μ₀ : Ω₀ → Measure ℂ) (D₀ : Ω₀ → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P₀ hC₀ hcirc₀ ∧ IsLQGMeasureOfField P₀ γ γ hcirc₀ μ₀ ∧ IsLQGMetricOfField P₀ γ ξ γ hC₀ D₀ := by
  obtain ⟨ξ, hξ, ⟨𝔇, h𝔇⟩, -⟩ := hMet γ hγ0 hγ2
  unfold WholePlaneGFFExistsFrozen at hGFF
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, hC₀, hcirc₀, hGFF₀⟩ := hGFF
  have hQ : γ < lqgQ γ := lt_lqgQ_of_mem_Ioo hγ0 hγ2
  obtain ⟨μ₀, hμ₀⟩ := hMeas Ω₀ P₀ hC₀ hcirc₀ hGFF₀ hγ0 hγ2 hQ
  have hI := (hAx Ω₀ P₀ γ ξ γ hC₀ hcirc₀ hGFF₀ hγ0 hγ2 hQ 𝔇 h𝔇).1
  refine ⟨ξ, hξ, Ω₀, mΩ₀, P₀, hP₀, hC₀, hcirc₀, μ₀,
    fun ω u v => (weylScaling (𝔇 (hC₀ ω)) ξ (fun x => -γ * Real.log ‖x‖) u v).toReal, hGFF₀, hμ₀, ?_⟩
  unfold IsLQGMetricOfField
  refine ⟨𝔇, h𝔇, ?_⟩
  filter_upwards [hI] with ω hω
  intro u v
  exact ⟨ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (ne_top_of_lt (hω.1 u v))⟩


end HarmonicBalls
