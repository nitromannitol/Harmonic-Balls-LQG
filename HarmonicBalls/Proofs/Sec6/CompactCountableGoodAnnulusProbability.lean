import HarmonicBalls.Proofs.Sec6.CompactUniformGoodAnnulus
import HarmonicBalls.Proofs.Sec6.GoodAnnulusPhaseProbability

/-! # Simultaneous good annuli for countable compact parameter families

The underlying fine-support argument uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess Metric
open scoped ENNReal Topology

universe u

/-- A pathwise common threshold and countable pointwise measurability give a
simultaneous high-probability bound. -/
theorem exists_countable_uniform_goodAnnulus_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ι : Type*} [Countable ι] {μ : Ω → Measure ℂ}
    (z : ι → ℂ) (r : ι → ℝ) {b : ℝ}
    (hmeas : ∀ i n, MeasurableSet
      {ω | IsGoodAnnulus (μ ω) (r i) (z i) ((1 / 2 : ℝ) ^ (n + 1)) b})
    (hae : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ ∀ i, IsGoodAnnulus (μ ω) (r i) (z i) a b)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      P {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) (r i) (z i) a b} ≤ δ := by
  classical
  let A : ℕ → Set Ω := fun n =>
    {ω | ¬ ∀ i, IsGoodAnnulus (μ ω) (r i) (z i) ((1 / 2 : ℝ) ^ (n + 1)) b}
  have hA : ∀ n, NullMeasurableSet (A n) P := by
    intro n
    have heq : A n = (⋂ i, {ω | IsGoodAnnulus (μ ω) (r i) (z i)
        ((1 / 2 : ℝ) ^ (n + 1)) b})ᶜ := by
      ext ω
      simp [A]
    rw [heq]
    exact (MeasurableSet.compl (MeasurableSet.iInter fun i => hmeas i n)).nullMeasurableSet
  have hanti : Antitone A := by
    intro m n hmn ω hbad hgood
    apply hbad
    intro i
    exact isGoodAnnulus_mono_mass (hgood i)
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.add_le_add_right hmn 1))
  have hi : P (⋂ n, A n) = 0 := by
    apply measure_mono_null _ (ae_iff.1 hae)
    intro ω hω hex
    obtain ⟨a, ha, hgood⟩ := hex
    have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    obtain ⟨n, hn⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_nhds ha))
    have hsmall : (1 / 2 : ℝ) ^ (n + 1) < a :=
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)).trans_lt (hn n le_rfl)
    have hbad := mem_iInter.1 hω n
    apply hbad
    intro i
    exact isGoodAnnulus_mono_mass (hgood i) hsmall.le
  have hlim := tendsto_measure_iInter_atTop (μ := P)
    (fun n => hA n) hanti ⟨0, measure_ne_top P _⟩
  rw [hi] at hlim
  obtain ⟨n, hn⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_nhds hδ))
  refine ⟨(1 / 2 : ℝ) ^ (n + 1), ⟨by positivity, ?_⟩, ?_⟩
  · exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  · have heq : {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) (r i) (z i)
        ((1 / 2 : ℝ) ^ (n + 1)) b} = A n := by
      ext ω
      simp only [A, mem_ofPred_eq, not_forall]
    rw [heq]
    exact (hn n le_rfl).le

/-- On compact centre sets and compact positive radius sets, the high-probability
bound holds simultaneously for any given countable family of parameter pairs. -/
theorem exists_compact_countable_goodAnnulus_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {K : Set ℂ} (hK : IsCompact K) {R : Set ℝ} (hR : IsCompact R) (hRpos : R ⊆ Ioi 0)
    {ι : Type*} [Countable ι] (z : ι → ℂ) (r : ι → ℝ)
    (hz : ∀ i, z i ∈ K) (hr : ∀ i, r i ∈ R)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      P {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) (r i) (z i) a b} ≤ δ := by
  let := h.isProbabilityMeasure
  have hm := h.aemeasurable_lqgMeasure hμ
  let ν := hm.mk μ
  have hν : Measurable ν := hm.measurable_mk
  have hμν : μ =ᵐ[P] ν := hm.ae_eq_mk
  have hae : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      ∀ i, IsGoodAnnulus (ν ω) (r i) (z i) a b := by
    filter_upwards [ae_compact_goodAnnulus_thresholds_of_volumeGrowth hgrowth hγ hγ2 h hμ,
      hμν] with ω hgood heq
    obtain ⟨a, ha, hgood⟩ := hgood K hK R hR hRpos b hb
    refine ⟨a, ha, ?_⟩
    intro i
    rw [← heq]
    exact hgood (z i) (hz i) (r i) (hr i)
  have hmeas : ∀ i n, MeasurableSet
      {ω | IsGoodAnnulus (ν ω) (r i) (z i) ((1 / 2 : ℝ) ^ (n + 1)) b} := by
    intro i n
    exact (measurableSet_isGoodAnnulus_of_pos (r i) (hRpos (hr i)) (z i)
      ((1 / 2 : ℝ) ^ (n + 1)) b (by positivity)).preimage hν
  obtain ⟨a, ha, hbound⟩ := exists_countable_uniform_goodAnnulus_probability P z r hmeas hae hδ
  refine ⟨a, ha, ?_⟩
  have heq : {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) (r i) (z i) a b} =ᵐ[P]
      {ω | ∃ i, ¬ IsGoodAnnulus (ν ω) (r i) (z i) a b} := by
    filter_upwards [hμν] with ω hω
    simp only [hω]
  exact (measure_congr heq).le.trans hbound

/-- The same bound applies to an arbitrary random choice from the countable
family; measurability of the choice itself is not needed. -/
theorem exists_compact_countable_selector_goodAnnulus_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {K : Set ℂ} (hK : IsCompact K) {R : Set ℝ} (hR : IsCompact R) (hRpos : R ⊆ Ioi 0)
    {ι : Type*} [Countable ι] (z : ι → ℂ) (r : ι → ℝ)
    (hz : ∀ i, z i ∈ K) (hr : ∀ i, r i ∈ R)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ choice : Ω → ι,
      P {ω | ¬ IsGoodAnnulus (μ ω) (r (choice ω)) (z (choice ω)) a b} ≤ δ := by
  obtain ⟨a, ha, hbound⟩ := exists_compact_countable_goodAnnulus_probability
    hgrowth hγ hγ2 h hμ hK hR hRpos z r hz hr hb hδ
  refine ⟨a, ha, fun choice => ?_⟩
  apply (measure_mono ?_).trans hbound
  intro ω hbad
  exact ⟨choice ω, hbad⟩

end HarmonicBalls.Section6
