import HarmonicBalls.FirstPass.Phase2.LQGMetricXiPos

/-! # No γ-LQG metric has a nonpositive Weyl exponent

`not_isLQGMetric_of_xi_nonpos`: for `γ ∈ (0, 2)` and `ξ ≤ 0`, no map `𝔇 : h ↦ D_h` is a γ-LQG metric with Weyl
exponent `ξ` (`IsLQGMetric γ ξ 𝔇`, `Defs/LQGMetric.lean`).

Argument (exact scaling at the origin, `isLQGMetric_xi_pos`, `FirstPass/Phase2/LQGMetricXiPos.lean`). Take a
whole-plane GFF `h` on a probability space in `Type`. By the coordinate change (axiom IV) at radius `r` and the Weyl
scaling (axiom III) by the constant `h_r(0) + Q log r`, almost surely
`D_h(r, 0) = e^{ξ (h_r(0) + Q log r)} D_{h̃_r}(1, 0)` with `h̃_r = h(r ·) - h_r(0)`, which is again a whole-plane GFF,
so `D_{h̃_r}(1, 0)` has the law of `D_h(1, 0)`, which is a.s. positive (axiom I). On the event `h_r(0) ≤ 0`, of
probability at least `1/2`, the factor is at least `1` when `ξ ≤ 0` and `r < 1`. This contradicts
`D_h(r, 0) → D_h(0, 0) = 0` almost surely as `r → 0` (axiom I: `D_h` induces the Euclidean topology).
-/

namespace HarmonicBalls

/-- **The Weyl exponent of a γ-LQG metric is positive.** For `γ ∈ (0, 2)` and `ξ ≤ 0` there is no γ-LQG metric with
Weyl exponent `ξ`: the exact scale invariance in law of `D_h(r, 0)` up to the factor `e^{ξ (h_r(0) + Q log r)}`
contradicts the continuity of `D_h` at the origin. -/
theorem not_isLQGMetric_of_xi_nonpos {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hξ : ξ ≤ 0)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) : ¬ IsLQGMetric γ ξ 𝔇 := fun h𝔇 =>
  not_lt.2 hξ (isLQGMetric_xi_pos γ ξ 𝔇 hγ hγ2 h𝔇)

end HarmonicBalls
