import HarmonicBalls.Proofs.Sec6.SingularCollarGoodAnnulusCounts
import HarmonicBalls.Proofs.Sec6.RootedRelativeCollar
import HarmonicBalls.Proofs.Sec6.RelativeCollarScaling
import HarmonicBalls.Proofs.Sec6.TranslatedCircleNull

/-! # Relative collars for a singular reference field

The imported Section 6 development uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The scaling law uses the
staged affine and coordinate-change hypotheses. -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal Topology
universe u

/-- A singular field centred at the origin has one relative collar width
whose failure probability is small at every positive scale. This is a
fixed-centre reference estimate, not a sampled-root statement. -/
theorem exists_singular_reference_uniform_relative_collar
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α hC hcirc)
    {c : ℝ} (hc : 0 < c) {d q : ℝ≥0∞} (hd : 0 < d) (hq : 0 < q) :
    ∃ η : ℝ, 0 < η ∧ η < c ∧ ∀ r : ℝ, 0 < r →
      P {ω | RelativeCollarFailure (μ ω) r η d} < q := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  obtain ⟨_, _, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hα h hμ
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ α hγ hγ2 hα
    Ω P hC hcirc μ h hμ
  have hpow := ae_singular_lqg_eq_power_weight hgrowth hγ hγ2 hα h hμ hμ₀
  have h3 := ae_lqg_sphere_eq_zero_of_translation h hμ₀ hAff 0 3
  have h5 := ae_lqg_sphere_eq_zero_of_translation h hμ₀ hAff 0 5
  have hne : (annulus (0 : ℂ) 3 5).Nonempty := by
    refine ⟨(4 : ℂ), ?_⟩
    norm_num [annulus, mem_ball, mem_closedBall, dist_eq_norm]
  have hreg : ∀ᵐ ω ∂P, μ ω (sphere 0 3) = 0 ∧ μ ω (sphere 0 5) = 0 ∧
      0 < μ ω (annulus 0 3 5) := by
    filter_upwards [hpow, h3, h5, hfull] with ω hw h3 h5 hf
    refine ⟨?_, ?_, hf _ (isOpen_ball.sdiff isClosed_closedBall) hne⟩
    · rw [hw]
      exact withDensity_absolutelyContinuous _ _ h3
    · rw [hw]
      exact withDensity_absolutelyContinuous _ _ h5
  obtain ⟨ν, hν, hνloc, heq⟩ := exists_measurable_locallyFinite_rep
    (h.aemeasurable_lqgMeasure hμ) (hV.mono fun _ hv => hv.1)
  let E : ℕ → Set Ω := fun n => {ω | RelativeCollarFailure (ν ω) 1 (1 / ((n : ℝ) + 1)) d}
  have hE (n : ℕ) : MeasurableSet (E n) :=
    (measurableSet_relativeCollarFailure 1 (1 / ((n : ℝ) + 1)) d).preimage hν
  have hlim : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ E n ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [hreg, heq] with ω hr he
    have hr' : ν ω (sphere 0 3) = 0 ∧ ν ω (sphere 0 5) = 0 ∧
        0 < ν ω (annulus 0 3 5) := by simpa only [← he] using hr
    let : IsLocallyFiniteMeasure (ν ω) := hνloc ω
    have ht := tendsto_twoSided_annulus_collar_mass_zero (ν ω) 0 3 5 hr'.1 hr'.2.1
    have hp : 0 < d * ν ω (annulus 0 3 5) := ENNReal.mul_pos hd.ne' hr'.2.2.ne'
    filter_upwards [ht.eventually_lt_const hp] with n hn
    simpa [E, RelativeCollarFailure] using hn.le
  have ht : Tendsto (fun n => P (E n)) atTop (𝓝 0) := by
    simpa only [measure_empty] using
      tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop MeasurableSet.empty hE hlim
  have hw := tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hc)
  obtain ⟨n, hn, hnc⟩ := ((ht.eventually_lt_const hq).and hw).exists
  refine ⟨1 / ((n : ℝ) + 1), by positivity, hnc, ?_⟩
  intro r hr
  rw [← measure_relativeCollarFailure_scale hγ hγ2 hα h hμ hAff hCC hr]
  have hevent : P {ω | RelativeCollarFailure (μ ω) 1 (1 / ((n : ℝ) + 1)) d} = P (E n) := by
    apply measure_congr
    filter_upwards [heq] with ω he
    simp only [E, mem_ofPred_eq, he]
  simpa only [hevent] using hn

end HarmonicBalls.Section6
