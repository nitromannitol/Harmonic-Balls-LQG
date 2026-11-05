import HarmonicBalls.Proofs.Sec6.ReverseNearbyGoodAnnulusCounts
import HarmonicBalls.Proofs.Sec6.GoodAnnulusJointMeasurability
import Mathlib.MeasureTheory.Integral.Indicator

/-! # Probability of reverse good-annulus transfer -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal Topology

/-- For any prescribed convergent sequence of centres, the probability that
a nearby annulus is good but the reference annulus is not good at relaxed
thresholds tends to zero. -/
theorem tendsto_reverse_nearby_goodAnnulus_transfer_failure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (μ : Ω → Measure ℂ) (hμ : Measurable μ)
    (hloc : ∀ ω, IsLocallyFiniteMeasure (μ ω))
    {z : ℂ} {r a a' b b' : ℝ} (hr : 0 < r)
    (ha' : 0 < a') (ha : a' < a) (hb : 0 ≤ b) (hbb : b < b')
    (hreg : ∀ᵐ ω ∂P, μ ω (sphere z (3*r)) = 0 ∧
      μ ω (sphere z (5*r)) = 0 ∧ 0 < μ ω (annulus z (3*r) (5*r)))
    (w : ℕ → ℂ) (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun n => P {ω | IsGoodAnnulus (μ ω) r (w n) a b ∧
      ¬ IsGoodAnnulus (μ ω) r z a' b'}) atTop (𝓝 0) := by
  have ha_pos : 0 < a := ha'.trans ha
  let E : ℕ → Set Ω := fun n => {ω | IsGoodAnnulus (μ ω) r (w n) a b ∧
    ¬ IsGoodAnnulus (μ ω) r z a' b'}
  have hE (n : ℕ) : MeasurableSet (E n) := by
    have h1 := measurableSet_isGoodAnnulus_joint hμ hloc
      (show Measurable (fun _ : Ω => w n) from measurable_const)
      (show Measurable (fun _ : Ω => r) from measurable_const) (fun _ => hr) ha_pos b
    have h2 := measurableSet_isGoodAnnulus_joint hμ hloc
      (show Measurable (fun _ : Ω => z) from measurable_const)
      (show Measurable (fun _ : Ω => r) from measurable_const) (fun _ => hr) ha' b'
    exact h1.inter h2.compl
  have hlim : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ E n ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [hreg] with ω ⟨h3, h5, hp⟩
    let : IsLocallyFiniteMeasure (μ ω) := hloc ω
    have hf : μ ω (annulus z (3*r) (5*r)) ≠ ∞ :=
      ne_top_of_le_ne_top measure_ball_ne_top (measure_mono sdiff_subset)
    obtain ⟨δ, hδ, hnear⟩ := exists_reverse_nearby_goodAnnulus (μ ω) z hr h3 h5 hp hf
      ha'.le ha hb hbb
    filter_upwards [(Metric.tendsto_nhds.mp hw) δ hδ] with n hn
    simp only [E, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
    exact hnear (w n) hn
  simpa only [measure_empty] using
    tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop MeasurableSet.empty hE hlim

/-- The reverse transfer-failure probability is uniformly small over all
centres in a deterministic neighbourhood of the reference centre. This bounds
each event separately; it does not bound their union. -/
theorem exists_uniform_reverse_goodAnnulus_transfer_failure_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (μ : Ω → Measure ℂ) (hμ : Measurable μ)
    (hloc : ∀ ω, IsLocallyFiniteMeasure (μ ω))
    {z : ℂ} {r a a' b b' : ℝ} (hr : 0 < r)
    (ha' : 0 < a') (ha : a' < a) (hb : 0 ≤ b) (hbb : b < b')
    (hreg : ∀ᵐ ω ∂P, μ ω (sphere z (3*r)) = 0 ∧
      μ ω (sphere z (5*r)) = 0 ∧ 0 < μ ω (annulus z (3*r) (5*r)))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z < δ →
      P {ω | IsGoodAnnulus (μ ω) r w a b ∧
        ¬ IsGoodAnnulus (μ ω) r z a' b'} < ε := by
  classical
  by_contra hn
  push Not at hn
  have hex (n : ℕ) : ∃ w : ℂ, dist w z < 1 / ((n : ℝ) + 1) ∧
      ε ≤ P {ω | IsGoodAnnulus (μ ω) r w a b ∧
        ¬ IsGoodAnnulus (μ ω) r z a' b'} :=
    hn _ (by positivity)
  choose w hw hbad using hex
  have hwt : Tendsto w atTop (𝓝 z) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    have he := tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hδ)
    filter_upwards [he] with n hn
    exact (hw n).trans hn
  have ht := tendsto_reverse_nearby_goodAnnulus_transfer_failure P μ hμ hloc hr
    ha' ha hb hbb hreg w hwt
  obtain ⟨n, hn⟩ := (ht.eventually (Iio_mem_nhds hε)).exists
  exact (not_lt_of_ge (hbad n)) hn

end HarmonicBalls.Section6
