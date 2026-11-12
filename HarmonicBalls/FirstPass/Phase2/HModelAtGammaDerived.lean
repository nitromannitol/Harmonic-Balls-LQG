import HarmonicBalls.FirstPass.S11r
import HarmonicBalls.FirstPass.Phase2.GFFExistsDerived2
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsDerived
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived
import HarmonicBalls.Proofs.GFF.LQGMetricUniquenessDerived

/-!
# Realization of the whole-plane model at insertion `γ`, without inputs

`hmodel_at_gamma` (`FirstPass/S11r.lean`) builds, for `γ ∈ (0, 2)`, a whole-plane GFF realization carrying an LQG
measure and an LQG metric at insertion `γ`, from four inputs: existence of a whole-plane GFF, existence of the LQG
measure, the field axioms of the LQG metric, and existence and uniqueness of the LQG metric. All four are now theorems
(`wholePlaneGFFExistsFrozen_derived'`, `lqgMeasureExistence_derived`, `lqgMetricFieldAxiomsUnivFrozen_derived`,
`lqgMetricExistenceUniqueness_derived`), so the realization holds outright: `hmodel_at_gamma_derived`.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- **Realization at `(γ, ξ, γ)`, no inputs**: for `γ ∈ (0, 2)` there are `ξ > 0` and a whole-plane GFF realization
with an LQG measure and an LQG metric of Weyl exponent `ξ` at insertion `γ`. -/
theorem hmodel_at_gamma_derived {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ (Ω₀ : Type u) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (hC₀ : Ω₀ → (ℂ → ℝ) → ℝ) (hcirc₀ : Ω₀ → ℝ → ℂ → ℝ) (μ₀ : Ω₀ → Measure ℂ) (D₀ : Ω₀ → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P₀ hC₀ hcirc₀ ∧ IsLQGMeasureOfField P₀ γ γ hcirc₀ μ₀ ∧ IsLQGMetricOfField P₀ γ ξ γ hC₀ D₀ :=
  hmodel_at_gamma.{u} wholePlaneGFFExistsFrozen_derived' hγ0 hγ2
    (fun _ _ P hC hcirc => lqgMeasureExistence_derived P γ γ hC hcirc)
    lqgMetricFieldAxiomsUnivFrozen_derived lqgMetricExistenceUniqueness_derived

end HarmonicBalls
