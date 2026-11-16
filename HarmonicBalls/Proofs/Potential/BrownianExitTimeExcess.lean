import HarmonicBalls.Proofs.Potential.GreenOccupationTail

/-! # Brownian exit-time excess

The expected excess of the exit time over a deterministic horizon vanishes at infinity.
-/

open MeasureTheory Set Filter MarkovProcess HarmonicBalls HarmonicBalls.Section6
open scoped ENNReal Topology

namespace HarmonicBalls.GreenOccupation

/-- For a nonnegative horizon, exit-time excess is post-horizon occupation of one. -/
theorem lintegral_exitTime_sub_eq_occupation_tail {D : Set ℂ} (x : ℂ)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ p, ContinuousPath.exitTime D p - ENNReal.ofReal T ∂planarBrownianMotion x) =
      ∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ),
        (Set.Ioi T).indicator (fun t =>
          {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p}.indicator
            (fun _ => (1 : ℝ≥0∞)) t) t) ∂planarBrownianMotion x := by
  apply lintegral_congr
  intro p
  let τ := ContinuousPath.exitTime D p
  let S : Set ℝ := {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < τ}
  have hS : MeasurableSet S := measurableSet_lt
    (measurable_coe_nnreal_ennreal.comp measurable_real_toNNReal) measurable_const
  change τ - ENNReal.ofReal T = ∫⁻ t in Set.Ioi (0 : ℝ),
    (Set.Ioi T).indicator (S.indicator (fun _ => (1 : ℝ≥0∞))) t
  rw [lintegral_indicator measurableSet_Ioi, lintegral_indicator hS, setLIntegral_one,
    Measure.restrict_apply hS, Measure.restrict_apply (hS.inter measurableSet_Ioi)]
  have hset : S ∩ Set.Ioi T ∩ Set.Ioi (0 : ℝ) = (S ∩ Set.Ioi 0) ∩ Set.Ioi T := by
    ext t
    simp only [mem_inter_iff]
    tauto
  rw [hset]
  by_cases hτ : τ = ⊤
  · have hs : S ∩ Set.Ioi 0 = Set.Ioi 0 := by
      simp [S, hτ]
    rw [hτ, ENNReal.top_sub ENNReal.ofReal_ne_top, hs]
    rw [Set.Ioi_inter_Ioi, max_eq_right hT, Real.volume_Ioi]
  · have hs : S ∩ Set.Ioi 0 = Set.Ioo 0 τ.toReal :=
      ContinuousPath.survivalSet_ne_top τ hτ
    rw [hs, Set.Ioo_inter_Ioi, max_eq_right hT,
      Real.volume_Ioo, ENNReal.ofReal_sub _ hT, ENNReal.ofReal_toReal hτ]

/-- The expected exit-time excess tends to zero for every bounded open set and starting point. -/
theorem tendsto_lintegral_exitTime_sub {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (x : ℂ) :
    Tendsto (fun T : ℝ => ∫⁻ p, ContinuousPath.exitTime D p - ENNReal.ofReal T
      ∂planarBrownianMotion x) atTop (𝓝 0) := by
  have hmeas := ContinuousPath.measurable_exitTime D hD
  have hfinite := lintegral_exitTime_planarBrownianMotion_lt_top hD hDb x
  have hae : ∀ᵐ p ∂planarBrownianMotion x, ContinuousPath.exitTime D p ≠ ⊤ :=
    (ae_lt_top hmeas hfinite.ne).mono fun _ h => h.ne
  have hlim : ∀ᵐ p ∂planarBrownianMotion x,
      Tendsto (fun T : ℝ => ContinuousPath.exitTime D p - ENNReal.ofReal T) atTop (𝓝 0) := by
    filter_upwards [hae] with p hp
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (ContinuousPath.exitTime D p).toReal] with T hT
    have hle : ContinuousPath.exitTime D p ≤ ENNReal.ofReal T := by
      rw [← ENNReal.ofReal_toReal hp]
      exact ENNReal.ofReal_le_ofReal hT
    simp [tsub_eq_zero_of_le hle]
  have h := tendsto_lintegral_filter_of_dominated_convergence
    (μ := planarBrownianMotion x) (l := atTop) (f := fun _ => 0)
    (fun p => ContinuousPath.exitTime D p)
    (Eventually.of_forall fun T => hmeas.sub measurable_const)
    (Eventually.of_forall fun T => Eventually.of_forall fun p => tsub_le_self)
    hfinite.ne hlim
  simpa only [lintegral_zero, Pi.sub_apply] using h

end HarmonicBalls.GreenOccupation
