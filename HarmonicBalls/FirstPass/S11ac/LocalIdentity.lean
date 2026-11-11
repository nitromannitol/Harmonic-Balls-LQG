import HarmonicBalls.Steps.Sec11.InternalMetricNear

/-! # Local identity of internal metrics on overlapping open sets

For a length metric `D` (`IsEuclideanLengthMetric D`) and open sets `Ua`, `Ub` containing `x`, the internal distances
`internalMetric D Ua x y` and `internalMetric D Ub x y` both equal `ofReal (D x y)` for all `y` close to `x`
(`IsEuclideanLengthMetric.internalMetric_eq_of_near`). Along any sequence converging to `x`, this holds eventually.
This is the input for the consistency of the piece constants in the punctured metric decoder.
-/

namespace HarmonicBalls.S11ac

open Set Filter Topology

variable {D : ℂ → ℂ → ℝ}

/-- The `D`-ball of radius `δ` about `x` is Euclidean-open (`D` induces the Euclidean topology). -/
theorem isOpen_dBall {x : ℂ} (hD : IsEuclideanLengthMetric D) {δ : ℝ} :
    IsOpen {z : ℂ | D x z < δ} := by
  rw [hD.isOpen_iff]
  intro z hz
  refine ⟨δ - D x z, by simp only [mem_ofPred_eq] at hz; linarith, fun w hw => ?_⟩
  simp only [mem_ofPred_eq] at hz ⊢
  have := hD.triangle x z w
  linarith

/-- Along a sequence converging to a point of two open sets, the internal distances of the two sets agree with the
length metric eventually. -/
theorem eventually_internalMetric_eq (hD : IsEuclideanLengthMetric D) (hnonneg : ∀ x y, 0 ≤ D x y)
    {Ua Ub : Set ℂ} (hUa : IsOpen Ua) (hUb : IsOpen Ub) {x : ℂ} (hxa : x ∈ Ua) (hxb : x ∈ Ub)
    {y : ℕ → ℂ} (hy : Tendsto y atTop (𝓝 x)) :
    ∀ᶠ n in atTop, internalMetric D Ua x (y n) = ENNReal.ofReal (D x (y n)) ∧
      internalMetric D Ub x (y n) = ENNReal.ofReal (D x (y n)) := by
  obtain ⟨δa, hδa, ha⟩ := hD.internalMetric_eq_of_near hnonneg hUa hxa
  obtain ⟨δb, hδb, hb⟩ := hD.internalMetric_eq_of_near hnonneg hUb hxb
  have hS : IsOpen {z : ℂ | D x z < min δa δb} := isOpen_dBall hD
  have hxS : x ∈ {z : ℂ | D x z < min δa δb} := by
    simp only [mem_ofPred_eq, hD.self_eq_zero]
    exact lt_min hδa hδb
  filter_upwards [hy.eventually (hS.mem_nhds hxS)] with n hn
  exact ⟨ha _ (lt_of_lt_of_le hn (min_le_left _ _)), hb _ (lt_of_lt_of_le hn (min_le_right _ _))⟩

end HarmonicBalls.S11ac

