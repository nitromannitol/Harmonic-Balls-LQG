import HarmonicBalls.Defs.LQGMetric

/-!
# Elementary facts on Euclidean length metrics

For `D : ℂ → ℂ → ℝ` with `IsEuclideanLengthMetric D` (Defs/LQGMetric.lean): `D ≥ 0` (from the diagonal, the
triangle inequality and symmetry), and `D(0, ·)` tends to `0` at `0` in the Euclidean topology, since the
`D`-balls around `0` are Euclidean open (`isOpen_iff`). Used for the a.s. convergence `D_h(0, r_n) → 0` in
the argument of `lqgMetricExponentPositive_of_inputs` (FirstPass/S11x.lean).
-/

namespace HarmonicBalls

open Filter Topology Set

/-- A Euclidean length metric is nonnegative. -/
theorem IsEuclideanLengthMetric.dist_nonneg {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (z w : ℂ) :
    0 ≤ D z w := by
  have h1 := hD.triangle z w z
  have h2 := hD.self_eq_zero z
  have h3 := hD.symm z w
  linarith

/-- For a Euclidean length metric `D`, `z ↦ D(0, z)` tends to `0` as `z → 0` in the Euclidean topology. -/
theorem IsEuclideanLengthMetric.tendsto_zero {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) :
    Tendsto (fun z => D 0 z) (𝓝 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hU : IsOpen {w | D 0 w < ε} := by
    rw [hD.isOpen_iff]
    intro z hz
    have hz' : D 0 z < ε := hz
    refine ⟨ε - D 0 z, by linarith, fun w hw => ?_⟩
    have ht := hD.triangle 0 z w
    show D 0 w < ε
    linarith
  have h0 : (0 : ℂ) ∈ {w | D 0 w < ε} := by
    show D 0 0 < ε
    rw [hD.self_eq_zero]
    exact hε
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU 0 h0
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδ] with z hz
  have hz' : D 0 z < ε := hball hz
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hD.dist_nonneg 0 z)]
  exact hz'

end HarmonicBalls
