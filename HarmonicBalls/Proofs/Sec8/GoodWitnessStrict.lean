import HarmonicBalls.Proofs.Sec8.GoodWitnessCompactExhaustion

/-! # Compact obstacles for strictly small witnesses

With a strict mass bound, one compact obstacle already suffices. The exact
non-strict bound requires the compact exhaustion from the preceding module.
-/

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

open MarkovProcess in
/-- A strictly small Borel witness can be enlarged to the complement of a
single compact obstacle, with strict mass and survival bounds preserved. -/
theorem exists_compact_obstacle_of_strict_badWitness
    (μ : Measure ℂ) {U Y : Set ℂ} (hU : IsOpen U)
    (hY : MeasurableSet Y) (hYU : Y ⊆ U) (hfinite : μ U ≠ ∞)
    (a b : ℝ≥0∞) (hmass : μ Y < a) (u : ℂ)
    (hp : b < planarBrownianMotion u
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Y p}) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ U ∧ μ (U \ K) < a ∧
      b < planarBrownianMotion u
        {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (U \ K) p} := by
  obtain ⟨K, hK, hmono, hsub, hsubset, heq⟩ :=
    exists_compact_obstacle_exhaustion hU.measurableSet hY hYU hfinite
  have hinf : (⨅ n, μ (U \ K n)) < a := by
    rw [← measure_sdiff_iUnion_compact_eq_iInf μ hU.measurableSet hfinite K hK hmono, heq]
    exact hmass
  obtain ⟨n, hn⟩ := iInf_lt_iff.mp hinf
  refine ⟨K n, hK n, (hsub n).trans sdiff_subset, hn, ?_⟩
  refine hp.trans_le (measure_mono ?_)
  intro p hp'
  apply hp'.trans (ContinuousPath.exitTime_mono ?_ p)
  exact hsubset.trans (sdiff_subset_sdiff_right (subset_iUnion K n))

end HarmonicBalls
