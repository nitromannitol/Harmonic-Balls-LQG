import HarmonicBalls.Proofs.Sec5.UniformBufferedContainment
import HarmonicBalls.Proofs.Sec8.OpenBallDensity

/-! # Measurable regularity events for LQG measure laws -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped ENNReal

universe u

/-- Local finiteness is measurable for the evaluation sigma algebra on planar measures. -/
theorem measurableSet_isLocallyFiniteMeasure_complex :
    MeasurableSet {ν : Measure ℂ | IsLocallyFiniteMeasure ν} := by
  have heq : {ν : Measure ℂ | IsLocallyFiniteMeasure ν} =
      ⋂ n : ℕ, {ν : Measure ℂ | ν (closedBall 0 n) < ∞} := by
    ext ν
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h n
      let _ := h
      exact (isCompact_closedBall (0 : ℂ) n).measure_lt_top
    · intro h
      constructor
      intro x
      obtain ⟨n, hn⟩ := exists_nat_gt (dist x (0 : ℂ))
      refine ⟨ball 0 n, isOpen_ball.mem_nhds ?_, ?_⟩
      · exact hn
      · exact lt_of_le_of_lt (measure_mono ball_subset_closedBall) (h n)
  rw [heq]
  exact MeasurableSet.iInter fun n =>
    measurableSet_lt (Measure.measurable_coe isClosed_closedBall.measurableSet) measurable_const

/-- Local finiteness holds almost surely under the law of a measurable random measure. -/
theorem ae_isLocallyFiniteMeasure_map
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    (hμ : AEMeasurable μ P) (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω)) :
    ∀ᵐ ν ∂Measure.map μ P, IsLocallyFiniteMeasure ν :=
  (ae_map_iff hμ measurableSet_isLocallyFiniteMeasure_complex).2 hloc

/-- The LQG measure law is concentrated on locally finite measures. -/
theorem IsWholePlaneGFF.ae_isLocallyFiniteMeasure_lqgMeasureLaw
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ν ∂Measure.map μ P, IsLocallyFiniteMeasure ν := by
  apply ae_isLocallyFiniteMeasure_map (hGFF.aemeasurable_lqgMeasure hμ)
  filter_upwards [hμ] with ω hω
  exact hω.isLocallyFiniteMeasure

/-- Volume-growth bounds on dyadic balls at a countable collection of centres
form a measurable event in the space of measures. -/
theorem measurableSet_eventually_dyadic_ball_bounds
    {ι : Type*} [Countable ι] (e : ι → ℂ) (βm βp : ℝ) :
    MeasurableSet {ν : Measure ℂ | ∃ N : ℕ, ∀ n ≥ N, ∀ i,
      ENNReal.ofReal (dyadicScale n ^ βm) ≤ ν (ball (e i) (dyadicScale n)) ∧
      ν (ball (e i) (dyadicScale n)) ≤ ENNReal.ofReal (dyadicScale n ^ βp)} := by
  simp only [ofPred_exists, ofPred_forall, ofPred_and]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun i =>
      (measurableSet_le measurable_const (Measure.measurable_coe isOpen_ball.measurableSet)).inter
        (measurableSet_le (Measure.measurable_coe isOpen_ball.measurableSet) measurable_const)

/-- Volume growth supplies the countable dyadic bounds simultaneously at any
chosen family of centres in the disc. -/
theorem VolumeGrowth.eventually_dyadic_ball_bounds
    {ι : Type*} {ν : Measure ℂ} {R βm βp : ℝ}
    (hV : VolumeGrowth ν R βm βp) (e : ι → ball (0 : ℂ) R) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i,
      ENNReal.ofReal (dyadicScale n ^ βm) ≤ ν (ball (e i) (dyadicScale n)) ∧
      ν (ball (e i) (dyadicScale n)) ≤ ENNReal.ofReal (dyadicScale n ^ βp) := by
  obtain ⟨_, _, r₀, hr₀, hbound⟩ := hV
  have hsmall : ∀ᶠ n in atTop, dyadicScale n < r₀ :=
    (tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds).eventually (Iio_mem_nhds hr₀)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  exact ⟨N, fun n hn i => hbound _ (dyadicScale_pos n) (hN n hn) (e i) (e i).property⟩

/-- Under the LQG measure law, the dyadic bounds hold simultaneously at any
countable family of centres, with deterministic exponents. -/
theorem IsWholePlaneGFF.ae_dyadic_ball_bounds_lqgMeasureLaw
    {Ω ι : Type u} [MeasurableSpace Ω] [Countable ι] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {R : ℝ} (hR : 0 < R) (e : ι → ball (0 : ℂ) R) :
    ∃ βm βp : ℝ, 0 < βm ∧ 0 < βp ∧
      ∀ᵐ ν ∂Measure.map μ P, ∃ N : ℕ, ∀ n ≥ N, ∀ i,
        ENNReal.ofReal (dyadicScale n ^ βm) ≤ ν (ball (e i) (dyadicScale n)) ∧
        ν (ball (e i) (dyadicScale n)) ≤ ENNReal.ofReal (dyadicScale n ^ βp) := by
  obtain ⟨βp, βm, hβp, hβp', hβm, hβm0⟩ := exists_volumeGrowth_exponents hγ hγ2 hα
  refine ⟨βm, βp, hβm0, hβp, ?_⟩
  apply (ae_map_iff (hGFF.aemeasurable_lqgMeasure hμ)
    (measurableSet_eventually_dyadic_ball_bounds (fun i => (e i : ℂ)) βm βp)).2
  filter_upwards [ae_isLocallyFiniteMeasure_volumeGrowth_of_exponents hI2 hγ hγ2 hα
    hβp hβp' hβm hGFF hμ] with ω hω
  exact (hω.2 R hR).eventually_dyadic_ball_bounds e

end HarmonicBalls
