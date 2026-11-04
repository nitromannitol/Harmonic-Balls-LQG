import HarmonicBalls.Proofs.Sec6.UniformGoodAnnulusFineSupport
import HarmonicBalls.Proofs.Sec6.GoodAnnulusProbabilityZeroExistence

/-! # Phase-uniform good-annulus probability

The imported fine-support and annulus iteration arguments use Leonardo Bonanno's
proof in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. Zero-strength
LQG existence is a staged input pending source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter
open scoped ENNReal Topology

universe u

/-- A countable diagonal argument obtains a uniform probability bound from
almost-sure uniformity and measurability at each individual radius. -/
theorem uniform_goodAnnulus_probability_of_pointwise_measurability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {μ : Ω → Measure ℂ} {S : Set ℝ} {b : ℝ} {z : ℂ}
    (hmeas : ∀ r ∈ S, ∀ n : ℕ, MeasurableSet
      {ω | IsGoodAnnulus (μ ω) r z ((1 / 2 : ℝ) ^ (n + 1)) b})
    (hae : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ ∀ r ∈ S, IsGoodAnnulus (μ ω) r z a b)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ r ∈ S,
      P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} ≤ ENNReal.ofReal (1 - p) := by
  classical
  by_contra hnone
  have hex (n : ℕ) : ∃ r ∈ S,
      ENNReal.ofReal (1 - p) <
        P {ω | ¬ IsGoodAnnulus (μ ω) r z ((1 / 2 : ℝ) ^ (n + 1)) b} := by
    by_contra hn
    push Not at hn
    apply hnone
    exact ⟨_, ⟨by positivity, pow_lt_one₀ (by norm_num) (by norm_num) (by omega)⟩, hn⟩
  choose s hs hbad using hex
  have hmeas' (n : ℕ) : NullMeasurableSet
      {ω | ∀ r ∈ range s, IsGoodAnnulus (μ ω) r z ((1 / 2 : ℝ) ^ (n + 1)) b} P := by
    have hm : MeasurableSet {ω | ∀ i : ℕ,
        IsGoodAnnulus (μ ω) (s i) z ((1 / 2 : ℝ) ^ (n + 1)) b} := by
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => hmeas (s i) (hs i) n
    simpa only [forall_mem_range] using hm.nullMeasurableSet
  have hae' : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      ∀ r ∈ range s, IsGoodAnnulus (μ ω) r z a b := by
    filter_upwards [hae] with ω hω
    obtain ⟨a, ha, hgood⟩ := hω
    exact ⟨a, ha, fun r hr => hgood r (by obtain ⟨i, rfl⟩ := hr; exact hs i)⟩
  obtain ⟨a, ha, hbound⟩ :=
    exists_uniform_goodAnnulus_threshold_of_measurable_events P hmeas' hae' hp
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨n, hn⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_nhds ha.1))
  have hsmall : (1 / 2 : ℝ) ^ (n + 1) ≤ a :=
    ((pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)).trans_lt
      (hn n le_rfl)).le
  have hsub : {ω | ¬ IsGoodAnnulus (μ ω) (s n) z ((1 / 2 : ℝ) ^ (n + 1)) b} ⊆
      {ω | ¬ IsGoodAnnulus (μ ω) (s n) z a b} := by
    intro ω hbadω hgoodω
    exact hbadω (isGoodAnnulus_mono_mass hgoodω hsmall)
  exact (not_lt_of_ge ((measure_mono hsub).trans (hbound (s n) (mem_range_self n)))) (hbad n)

/-- Volume growth implies a probability bound uniform over the compact
interval of dyadic phases. -/
theorem uniform_goodAnnulus_probability_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b p : ℝ} (hb : 0 < b) (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Icc (1 / 2 : ℝ) 1,
      P {ω | ¬ IsGoodAnnulus (μ ω) r 0 a b} ≤ ENNReal.ofReal (1 - p) := by
  let := h.isProbabilityMeasure
  have hm := h.aemeasurable_lqgMeasure hμ
  let ν := hm.mk μ
  have hν : Measurable ν := hm.measurable_mk
  have hμν : μ =ᵐ[P] ν := hm.ae_eq_mk
  have hae : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      ∀ r ∈ Icc (1 / 2 : ℝ) 1, IsGoodAnnulus (ν ω) r 0 a b := by
    filter_upwards [ae_uniform_goodAnnulus_threshold_on_dyadic_phases hgrowth hγ hγ2 h hμ,
      hμν] with ω hω heqω
    simpa only [← heqω] using hω 0 b hb
  obtain ⟨a, ha, hbound⟩ := uniform_goodAnnulus_probability_of_pointwise_measurability P
    (μ := ν) (fun r hr n => (measurableSet_isGoodAnnulus_of_pos r (by linarith [hr.1]) 0
      ((1 / 2 : ℝ) ^ (n + 1)) b (by positivity)).preimage hν) hae hp
  refine ⟨a, ha, ?_⟩
  intro r hr
  have heq : P {ω | ¬ IsGoodAnnulus (μ ω) r 0 a b} =
      P {ω | ¬ IsGoodAnnulus (ν ω) r 0 a b} := by
    apply measure_congr
    filter_upwards [hμν] with ω hω
    simp only [hω]
  rw [heq]
  exact hbound r hr

/-- Lemma 6.4 from volume growth and staged zero-strength LQG existence. -/
theorem goodAnnulusProbabilityStmt_of_volumeGrowth_zero_existence
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc) : GoodAnnulusProbabilityStmt.{u} := by
  apply goodAnnulusProbabilityStmt_of_dyadic_phase_and_zero_existence ?_ hE0
  intro γ hγ hγ2 b hb p hp Ω _ P hC hcirc μ h hμ
  obtain ⟨a, ha, hbound⟩ :=
    uniform_goodAnnulus_probability_of_volumeGrowth hgrowth hγ hγ2 h hμ hb.1 hp
  exact ⟨a, ha, fun r hr => hbound r ⟨hr.1.le, hr.2⟩⟩

end HarmonicBalls.Section6
