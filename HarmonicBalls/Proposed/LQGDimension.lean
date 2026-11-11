import HarmonicBalls.Defs.LQGGraphDistance

/-!
# The Liouville graph-distance dimension

This literature input is staged pending source check.
-/

namespace HarmonicBalls

/-- **LQG graph-distance exponent.** Ding--Gwynne, *The fractal dimension of
Liouville quantum gravity: universality, monotonicity, and bounds*,
arXiv:1807.01072v3, Theorem 1.4, p. 6, equation (1.8), together with the
positivity of the dimension in Theorem 1.1, p. 4. For every normalized
whole-plane GFF, the graph-distance exponent between the fixed points `0` and
`1` is `1 / d_γ`, almost surely. The statement below restricts the full limit
to dyadic mass scales and fixes those points; the same deterministic dimension
is used for every realization of the normalized field. -/
def WholePlaneLQGGraphDimension : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ dimension, IsWholePlaneLQGDimension γ dimension

/-- The chosen dimension satisfies the graph-distance characterization when the input holds. -/
theorem lqgGraphDimension_spec (h : WholePlaneLQGGraphDimension) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) : IsWholePlaneLQGDimension γ (lqgGraphDimension γ) :=
  isWholePlaneLQGDimension_lqgGraphDimension (h γ hγ hγ2)

end HarmonicBalls
