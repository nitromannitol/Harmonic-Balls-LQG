import HarmonicBalls.Proofs.Sec6.CompactCountableGoodAnnulusProbability

/-! # Uniform probability bounds over countable annulus families

The underlying fine-support argument uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess Metric
open scoped ENNReal Topology

universe u

/-- A diagonal argument makes the threshold uniform over all countable
subfamilies of an arbitrary family with a common pathwise threshold. -/
theorem exists_uniform_over_countable_goodAnnulus_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {T : Type*} {μ : Ω → Measure ℂ} (z : T → ℂ) (r : T → ℝ) {b : ℝ}
    (hmeas : ∀ t n, MeasurableSet
      {ω | IsGoodAnnulus (μ ω) (r t) (z t) ((1 / 2 : ℝ) ^ (n + 1)) b})
    (hae : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ ∀ t, IsGoodAnnulus (μ ω) (r t) (z t) a b)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ f : ℕ → T,
      P {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) (r (f i)) (z (f i)) a b} ≤ δ := by
  classical
  by_contra h
  have hbad : ∀ n : ℕ, ∃ f : ℕ → T,
      δ < P {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) (r (f i)) (z (f i))
        ((1 / 2 : ℝ) ^ (n + 1)) b} := by
    intro n
    have hn : (1 / 2 : ℝ) ^ (n + 1) ∈ Ioo (0 : ℝ) 1 :=
      ⟨by positivity, pow_lt_one₀ (by norm_num) (by norm_num) (by omega)⟩
    by_contra hn'
    apply h
    refine ⟨_, hn, ?_⟩
    intro f
    exact le_of_not_gt (fun hf => hn' ⟨f, hf⟩)
  choose f hf using hbad
  let z' : ℕ × ℕ → ℂ := fun p => z (f p.1 p.2)
  let r' : ℕ × ℕ → ℝ := fun p => r (f p.1 p.2)
  have hmeas' : ∀ p n, MeasurableSet
      {ω | IsGoodAnnulus (μ ω) (r' p) (z' p) ((1 / 2 : ℝ) ^ (n + 1)) b} :=
    fun p n => hmeas (f p.1 p.2) n
  have hae' : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      ∀ p, IsGoodAnnulus (μ ω) (r' p) (z' p) a b := by
    filter_upwards [hae] with ω hω
    obtain ⟨a, ha, hgood⟩ := hω
    exact ⟨a, ha, fun p => hgood (f p.1 p.2)⟩
  obtain ⟨a, ha, hbound⟩ := exists_countable_uniform_goodAnnulus_probability P z' r' hmeas' hae' hδ
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨n, hn⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_nhds ha.1))
  have hsmall : (1 / 2 : ℝ) ^ (n + 1) ≤ a :=
    ((pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)).trans_lt
      (hn n le_rfl)).le
  have hsub : {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) (r (f n i)) (z (f n i))
      ((1 / 2 : ℝ) ^ (n + 1)) b} ⊆
      {ω | ∃ p, ¬ IsGoodAnnulus (μ ω) (r' p) (z' p) a b} := by
    rintro ω ⟨i, hbad⟩
    refine ⟨(n, i), ?_⟩
    intro hgood
    exact hbad (isGoodAnnulus_mono_mass hgood hsmall)
  exact (not_lt_of_ge ((measure_mono hsub).trans hbound)) (hf n)

/-- One deterministic threshold controls every countable family in the fixed
compact centre and positive-radius sets. -/
theorem exists_compact_uniform_countable_goodAnnulus_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {K : Set ℂ} (hK : IsCompact K) {R : Set ℝ} (hR : IsCompact R) (hRpos : R ⊆ Ioi 0)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (z : ℕ → ℂ) (r : ℕ → ℝ),
      (∀ i, z i ∈ K) → (∀ i, r i ∈ R) →
      P {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) (r i) (z i) a b} ≤ δ := by
  let := h.isProbabilityMeasure
  have hm := h.aemeasurable_lqgMeasure hμ
  let ν := hm.mk μ
  have hν : Measurable ν := hm.measurable_mk
  have hμν : μ =ᵐ[P] ν := hm.ae_eq_mk
  let T := {p : ℂ × ℝ // p.1 ∈ K ∧ p.2 ∈ R}
  let zT : T → ℂ := fun t => t.1.1
  let rT : T → ℝ := fun t => t.1.2
  have hmeas : ∀ t n, MeasurableSet
      {ω | IsGoodAnnulus (ν ω) (rT t) (zT t) ((1 / 2 : ℝ) ^ (n + 1)) b} := by
    intro t n
    exact (measurableSet_isGoodAnnulus_of_pos (rT t) (hRpos t.2.2) (zT t)
      ((1 / 2 : ℝ) ^ (n + 1)) b (by positivity)).preimage hν
  have hae : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      ∀ t, IsGoodAnnulus (ν ω) (rT t) (zT t) a b := by
    filter_upwards [ae_compact_goodAnnulus_thresholds_of_volumeGrowth hgrowth hγ hγ2 h hμ,
      hμν] with ω hgood heq
    obtain ⟨a, ha, hgood⟩ := hgood K hK R hR hRpos b hb
    refine ⟨a, ha, ?_⟩
    intro t
    rw [← heq]
    exact hgood (zT t) t.2.1 (rT t) t.2.2
  obtain ⟨a, ha, hbound⟩ :=
    exists_uniform_over_countable_goodAnnulus_probability P zT rT hmeas hae hδ
  refine ⟨a, ha, ?_⟩
  intro z r hz hr
  let f : ℕ → T := fun i => ⟨(z i, r i), hz i, hr i⟩
  have heq : {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) (r i) (z i) a b} =ᵐ[P]
      {ω | ∃ i, ¬ IsGoodAnnulus (ν ω) (rT (f i)) (zT (f i)) a b} := by
    filter_upwards [hμν] with ω hω
    simp only [hω, f, rT, zT]
  exact (measure_congr heq).le.trans (hbound f)

/-- For a fixed singular limit, one deterministic threshold controls every
countable family in the fixed compact centre and positive-radius sets. -/
theorem exists_singular_compact_uniform_countable_goodAnnulus_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc)
    {K : Set ℂ} (hK : IsCompact K) {R : Set ℝ} (hR : IsCompact R) (hRpos : R ⊆ Ioi 0)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (z : ℕ → ℂ) (r : ℕ → ℝ),
      (∀ i, z i ∈ K) → (∀ i, r i ∈ R) →
      P {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) (r i) (z i) a b} ≤ δ := by
  let := h.isProbabilityMeasure
  have hm := h.aemeasurable_lqgMeasure hμ
  let ν := hm.mk μ
  have hν : Measurable ν := hm.measurable_mk
  have hμν : μ =ᵐ[P] ν := hm.ae_eq_mk
  let T := {p : ℂ × ℝ // p.1 ∈ K ∧ p.2 ∈ R}
  let zT : T → ℂ := fun t => t.1.1
  let rT : T → ℝ := fun t => t.1.2
  have hmeas : ∀ t n, MeasurableSet
      {ω | IsGoodAnnulus (ν ω) (rT t) (zT t) ((1 / 2 : ℝ) ^ (n + 1)) b} := by
    intro t n
    exact (measurableSet_isGoodAnnulus_of_pos (rT t) (hRpos t.2.2) (zT t)
      ((1 / 2 : ℝ) ^ (n + 1)) b (by positivity)).preimage hν
  have hae : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      ∀ t, IsGoodAnnulus (ν ω) (rT t) (zT t) a b := by
    filter_upwards [ae_all_singular_compact_goodAnnulus_thresholds_of_zero_existence
      hgrowth P γ hγ hγ2 hC hcirc h hE0, hμ, hμν] with ω hgood hlimit heq
    obtain ⟨a, ha, hgood⟩ := hgood α (μ ω) hlimit K hK R hR hRpos b hb
    refine ⟨a, ha, ?_⟩
    intro t
    rw [← heq]
    exact hgood (zT t) t.2.1 (rT t) t.2.2
  obtain ⟨a, ha, hbound⟩ :=
    exists_uniform_over_countable_goodAnnulus_probability P zT rT hmeas hae hδ
  refine ⟨a, ha, ?_⟩
  intro z r hz hr
  let f : ℕ → T := fun i => ⟨(z i, r i), hz i, hr i⟩
  have heq : {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) (r i) (z i) a b} =ᵐ[P]
      {ω | ∃ i, ¬ IsGoodAnnulus (ν ω) (rT (f i)) (zT (f i)) a b} := by
    filter_upwards [hμν] with ω hω
    simp only [hω, f, rT, zT]
  exact (measure_congr heq).le.trans (hbound f)

/-- A threshold chosen independently of the countable range also controls
any field-dependent choice from that range. -/
theorem exists_compact_uniform_countable_selector_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {K : Set ℂ} (hK : IsCompact K) {R : Set ℝ} (hR : IsCompact R) (hRpos : R ⊆ Ioi 0)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (z : ℕ → ℂ) (r : ℕ → ℝ),
      (∀ i, z i ∈ K) → (∀ i, r i ∈ R) → ∀ choice : Ω → ℕ,
      P {ω | ¬ IsGoodAnnulus (μ ω) (r (choice ω)) (z (choice ω)) a b} ≤ δ := by
  obtain ⟨a, ha, hbound⟩ := exists_compact_uniform_countable_goodAnnulus_probability
    hgrowth hγ hγ2 h hμ hK hR hRpos hb hδ
  refine ⟨a, ha, ?_⟩
  intro z r hz hr choice
  apply (measure_mono ?_).trans (hbound z r hz hr)
  intro ω hbad
  exact ⟨choice ω, hbad⟩

end HarmonicBalls.Section6
