import HarmonicBalls.Proofs.Sec2.GraphDistanceFinite
import HarmonicBalls.Proofs.Sec2.GraphDimensionScaleInterpolation

/-!
# Diagonal Liouville graph distance

We acknowledge Leonardo Bonanno's contributions to this formalization.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology

/-- A null point has graph distance one from itself at every positive threshold. -/
theorem liouvilleGraphDistance_self (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    {z : ℂ} (hz : μ {z} = 0) {ε : ℝ} (hε : 0 < ε) :
    liouvilleGraphDistance μ ε z z = 1 := by
  have h : μ ({z} : Set ℂ) < ENNReal.ofReal ε := by
    rw [hz]
    exact ENNReal.ofReal_pos.mpr hε
  obtain ⟨U, hU, hUopen, hUm⟩ := isCompact_singleton.exists_isOpen_lt_of_lt _ h
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hUopen z (hU (by simp))
  apply le_antisymm
  · apply liouvilleGraphDistance_le
    refine ⟨fun _ => (z, r), ?_, Path.refl z, ?_⟩
    · intro i
      exact ⟨hr, (measure_mono hrU).trans hUm.le⟩
    · intro t
      exact ⟨0, Metric.mem_ball_self hr⟩
  · exact one_le_liouvilleGraphDistance μ ε z z

/-- Every dyadic graph-distance exponent at a null point is zero. -/
theorem liouvilleGraphExponent_self (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    {z : ℂ} (hz : μ {z} = 0) (n : ℕ) : liouvilleGraphExponent μ z z n = 0 := by
  rw [liouvilleGraphExponent, liouvilleGraphDistance_self μ hz (dyadicScale_pos n)]
  simp only [ENat.toNat_one, Nat.cast_one, Real.log_one, zero_div]

/-- No positive finite graph dimension is characterized at a null point by the diagonal. -/
theorem not_isLiouvilleGraphDimension_self (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    {z : ℂ} (hz : μ {z} = 0) (d : ℝ) : ¬ IsLiouvilleGraphDimension μ z z d := by
  intro hd
  have hzero : Tendsto (liouvilleGraphExponent μ z z) atTop (𝓝 0) := by
    have hf : liouvilleGraphExponent μ z z = fun _ => 0 :=
      funext (liouvilleGraphExponent_self μ hz)
    rw [hf]
    exact tendsto_const_nhds
  have heq : (1 : ℝ) / d = 0 := tendsto_nhds_unique hd.2.2 hzero
  exact (ne_of_gt (one_div_pos.mpr hd.1)) heq

#print axioms liouvilleGraphDistance_self
#print axioms liouvilleGraphExponent_self
#print axioms not_isLiouvilleGraphDimension_self

end HarmonicBalls
