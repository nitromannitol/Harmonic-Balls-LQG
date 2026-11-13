import HarmonicBalls.Defs.LQGGraphDistance
import HarmonicBalls.Proofs.GFF.BackgroundChargeParameter
import HarmonicBalls.FirstPass.Phase2.GFFExistsDerived2
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived

/-!
# Uniqueness of the whole-plane Liouville graph-distance dimension

For `γ ∈ (0, 2)` there is a realization, on a probability space in `Type`, of a normalized whole-plane Gaussian free
field together with its LQG measure without singularity (`α₀ = 0`): the field exists by
`wholePlaneGFFExistsFrozen_derived'` and the Gaussian multiplicative chaos measure by `lqgMeasureExistence_derived`
(Duplantier-Sheffield, arXiv:0808.1560v2, Proposition 1.1). Since `IsWholePlaneLQGDimension γ d` asks for the
almost-sure graph-distance exponent `1 / d` on every such realization, a single realization identifies `d`
(Ding-Gwynne, arXiv:1807.01072v3, Theorem 1.4, equation (1.8), the exponent being a deterministic constant).
Consequently the chosen value `lqgGraphDimension γ` equals every characterized dimension, with no input.
-/

namespace HarmonicBalls

open MeasureTheory

/-- **A whole-plane GFF with its LQG measure exists in `Type`.** For `γ ∈ (0, 2)` some probability space carries a
normalized whole-plane GFF and an LQG measure of parameter `γ` without singularity. -/
theorem exists_wholePlaneGFF_lqgMeasureOfField_zero {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc ∧ IsLQGMeasureOfField P γ 0 hcirc μ := by
  obtain ⟨Ω, _, P, _, hC, hcirc, hG⟩ := wholePlaneGFFExistsFrozen_derived'.{0}
  obtain ⟨μ, hμ⟩ := lqgMeasureExistence_derived P γ 0 hC hcirc hG hγ0 hγ2 (lqgQ_pos hγ0)
  exact ⟨Ω, inferInstance, P, inferInstance, hC, hcirc, μ, hG, hμ⟩

/-- **Uniqueness of the LQG graph-distance dimension.** Two dimensions characterizing the almost-sure
Liouville graph-distance exponent of every normalized whole-plane GFF coincide. -/
theorem isWholePlaneLQGDimension_unique {γ dimension dimension' : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (h : IsWholePlaneLQGDimension γ dimension) (h' : IsWholePlaneLQGDimension γ dimension') :
    dimension = dimension' := by
  obtain ⟨Ω, _, P, _, hC, hcirc, μ, hG, hμ⟩ := exists_wholePlaneGFF_lqgMeasureOfField_zero hγ0 hγ2
  exact h.unique_of_realization h' Ω P hC hcirc μ hG hμ

/-- **The chosen dimension is the characterized one.** Whenever `dimension` characterizes the whole-plane
Liouville graph-distance exponent, `lqgGraphDimension γ = dimension`. -/
theorem lqgGraphDimension_eq_of_isWholePlaneLQGDimension {γ dimension : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (h : IsWholePlaneLQGDimension γ dimension) : lqgGraphDimension γ = dimension := by
  obtain ⟨Ω, _, P, _, hC, hcirc, μ, hG, hμ⟩ := exists_wholePlaneGFF_lqgMeasureOfField_zero hγ0 hγ2
  exact h.lqgGraphDimension_eq Ω P hC hcirc μ hG hμ

/-- **At most one dimension.** For `γ ∈ (0, 2)` the whole-plane graph-distance characterization has at most one
solution, so an existing one is unique. -/
theorem existsUnique_isWholePlaneLQGDimension {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (h : ∃ dimension, IsWholePlaneLQGDimension γ dimension) :
    ∃! dimension, IsWholePlaneLQGDimension γ dimension := by
  obtain ⟨dimension, hd⟩ := h
  exact ⟨dimension, hd, fun d' hd' => isWholePlaneLQGDimension_unique hγ0 hγ2 hd' hd⟩

end HarmonicBalls
