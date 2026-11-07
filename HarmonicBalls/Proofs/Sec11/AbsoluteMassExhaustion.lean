import HarmonicBalls.Proofs.Sec8.VagueMassConvergence

/-! # Absolute LQG mass along a continuity exhaustion -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- Jointly measurable local circle averages decode the absolute LQG mass of
an increasing bounded continuity exhaustion. -/
theorem IsWholePlaneGFF.exists_local_absolute_mass_of_exhaustion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {γ α : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (m : MeasurableSpace Ω)
    (E : ℕ → Set ℂ) (hEm : ∀ n, MeasurableSet (E n)) (hmono : Monotone E)
    (hbounded : Bornology.IsBounded (⋃ n, E n))
    (hfront : ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (E n)) = 0) ∧
      μ ω (frontier (⋃ n, E n)) = 0)
    (d : ℕ → Ω → ℂ → ℝ)
    (hdm : ∀ n, @Measurable (Ω × ℂ) ℝ (m.prod inferInstance) _ (Function.uncurry (d n)))
    (hdeq : ∀ n, ∀ᵐ ω ∂P, ∀ z ∈ E n,
      d n ω z = fieldCircleAverage α (hcirc ω) (dyadicScale n) z) :
    ∃ Y : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞ m _ Y ∧
      Y =ᵐ[P] fun ω => μ ω (⋃ n, E n) := by
  let A : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    (volume.withDensity fun z => ENNReal.ofReal
      ((dyadicScale n) ^ (γ ^ 2 / 2) * Real.exp (γ * d n ω z))) (E n)
  have hAm : ∀ n, @Measurable Ω ℝ≥0∞ m _ (A n) := by
    intro n
    apply (Measure.measurable_coe (hEm n)).comp
    apply measurable_withDensity
    exact (measurable_const.mul ((measurable_const.mul (hdm n)).exp)).ennreal_ofReal
  let Y : Ω → ℝ≥0∞ := fun ω => liminf (fun n => A n ω) atTop
  have hYm : @Measurable Ω ℝ≥0∞ m _ Y := by
    let : MeasurableSpace Ω := m
    exact Measurable.liminf hAm
  refine ⟨Y, hYm, ?_⟩
  have hd := ae_all_iff.mpr hdeq
  have hc := ae_all_iff.mpr fun n =>
    @IsWholePlaneGFF.ae_continuous_fieldCircleAverage Ω mΩ P hC hcirc hgff α _ (dyadicScale_pos n)
  filter_upwards [hμ, hc, hfront, hd] with ω hω hcω hfω hdω
  let ν : ℕ → Measure ℂ := fun n => lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale n)
  let : ∀ n, IsLocallyFiniteMeasure (ν n) := fun n =>
    isLocallyFiniteMeasure_lqgApprox_of_continuous γ _ _ (hcω n)
  let : IsLocallyFiniteMeasure (μ ω) := hω.isLocallyFiniteMeasure
  have hfixed (k : ℕ) : Tendsto (fun n => ν n (E k)) atTop (𝓝 (μ ω (E k))) :=
    tendsto_measure_of_tendsto_compactlySupported ν (μ ω) hω.tendsto_integral
      (hbounded.subset (subset_iUnion E k)) (hfω.1 k)
  have hunion : Tendsto (fun n => ν n (⋃ k, E k)) atTop (𝓝 (μ ω (⋃ k, E k))) :=
    tendsto_measure_of_tendsto_compactlySupported ν (μ ω) hω.tendsto_integral hbounded hfω.2
  have ht := tendsto_measure_exhaustion ν (μ ω) E hmono hfixed hunion
  have heq (n : ℕ) : A n ω = ν n (E n) := by
    dsimp [A, ν, lqgApprox]
    rw [withDensity_apply _ (hEm n), withDensity_apply _ (hEm n)]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (hEm n)] with z hz
    rw [hdω n z hz]
  have ht' : Tendsto (fun n => A n ω) atTop (𝓝 (μ ω (⋃ n, E n))) := by
    simpa only [heq] using ht
  exact ht'.liminf_eq

#print axioms IsWholePlaneGFF.exists_local_absolute_mass_of_exhaustion
end HarmonicBalls
