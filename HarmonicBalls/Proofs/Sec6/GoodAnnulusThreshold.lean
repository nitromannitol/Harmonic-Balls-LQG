import HarmonicBalls.Draft.Section6

/-!
# Measurable thresholds for good annuli

The good-annulus predicate quantifies over Borel sets, and its measurability as an event is
not immediate (GRAPH G16). A measurable positive random lower bound for its mass threshold
is sufficient to obtain a deterministic threshold with a bound on the outer probability of
the bad event. This isolates the measurable-witness requirement in Lemma 6.4.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- A good annulus remains good when its allowed mass is decreased. -/
theorem isGoodAnnulus_mono_mass {μ : Measure ℂ} {r a a' b : ℝ} {z : ℂ}
    (hg : IsGoodAnnulus μ r z a b) (ha : a' ≤ a) : IsGoodAnnulus μ r z a' b := by
  intro Y hY hYA hm u hu
  apply hg Y hY hYA _ u hu
  refine hm.trans ?_
  gcongr

/-- A positive measurable random threshold admits a positive deterministic lower quantile. -/
theorem exists_small_threshold {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {X : Ω → ℝ} (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 < X ω)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, P {ω | X ω < a} ≤ δ := by
  let A : ℕ → Set Ω := fun n => {ω | X ω ≤ (1 / 2 : ℝ) ^ n}
  have hA : ∀ n, MeasurableSet (A n) := fun n => measurableSet_le hX measurable_const
  have hanti : Antitone A := by
    intro m n hmn ω hω
    change X ω ≤ (1 / 2 : ℝ) ^ n at hω
    change X ω ≤ (1 / 2 : ℝ) ^ m
    exact hω.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn)
  have hi : P (⋂ n, A n) = 0 := by
    apply measure_mono_null _ (ae_iff.1 hpos)
    intro ω hω hωpos
    have hall : ∀ n : ℕ, X ω ≤ (1 / 2 : ℝ) ^ n := by
      simpa only [mem_iInter, A, mem_ofPred_eq] using hω
    have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    have hlt := hlim.eventually (eventually_lt_nhds hωpos)
    obtain ⟨n, hn⟩ := eventually_atTop.1 hlt
    exact (not_lt_of_ge (hall n)) (hn n le_rfl)
  have hlim := tendsto_measure_iInter_atTop (μ := P)
    (fun n => (hA n).nullMeasurableSet) hanti ⟨0, measure_ne_top P _⟩
  rw [hi] at hlim
  have hevent : ∀ᶠ n in atTop, P (A n) < δ := hlim.eventually (eventually_lt_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨(1 / 2 : ℝ) ^ (N + 1), ⟨by positivity, ?_⟩, ?_⟩
  · exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  · have hsub : {ω | X ω < (1 / 2 : ℝ) ^ (N + 1)} ⊆ A (N + 1) := by
      intro ω hω
      change X ω < (1 / 2 : ℝ) ^ (N + 1) at hω
      change X ω ≤ (1 / 2 : ℝ) ^ (N + 1)
      exact le_of_lt hω
    exact (measure_mono hsub).trans (hN (N + 1) (by omega)).le

/-- A measurable almost-sure lower bound on the random good-annulus threshold gives the
outer-probability estimate in Lemma 6.4 without assuming the good event is measurable. -/
theorem exists_goodAnnulus_threshold_of_measurable_witness
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {μ : Ω → Measure ℂ} {r b : ℝ} {z : ℂ} {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 < X ω)
    (hgood : ∀ᵐ ω ∂P, IsGoodAnnulus (μ ω) r z (X ω) b)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} ≤ ENNReal.ofReal (1 - p) := by
  obtain ⟨a, ha, hsmall⟩ := exists_small_threshold P hX hpos
    (ENNReal.ofReal_pos.2 (sub_pos.2 hp.2))
  refine ⟨a, ha, ?_⟩
  refine (measure_mono_ae ?_).trans hsmall
  filter_upwards [hgood] with ω hω hbad
  by_contra hnot
  exact hbad (isGoodAnnulus_mono_mass hω (le_of_not_gt hnot))

/-- If the countable family of dyadic good-annulus events is measurable, almost-sure existence
of some positive threshold implies a deterministic threshold with the prescribed probability.
The measurability hypothesis records the unresolved part of GRAPH G16. -/
theorem exists_goodAnnulus_threshold_of_measurable_events
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {μ : Ω → Measure ℂ} {r b : ℝ} {z : ℂ}
    (hmeas : ∀ n : ℕ, MeasurableSet
      {ω | IsGoodAnnulus (μ ω) r z ((1 / 2 : ℝ) ^ (n + 1)) b})
    (hae : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (μ ω) r z a b)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} ≤ ENNReal.ofReal (1 - p) := by
  let A : ℕ → Set Ω := fun n => {ω | ¬ IsGoodAnnulus (μ ω) r z ((1 / 2 : ℝ) ^ (n + 1)) b}
  have hA : ∀ n, MeasurableSet (A n) := fun n => (hmeas n).compl
  have hanti : Antitone A := by
    intro m n hmn ω hbad hgood
    apply hbad
    apply isGoodAnnulus_mono_mass hgood
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.add_le_add_right hmn 1)
  have hi : P (⋂ n, A n) = 0 := by
    apply measure_mono_null _ (ae_iff.1 hae)
    intro ω hω hex
    obtain ⟨a, ha, hgood⟩ := hex
    have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    obtain ⟨n, hn⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_nhds ha))
    have hsmall : (1 / 2 : ℝ) ^ (n + 1) < a :=
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)).trans_lt (hn n le_rfl)
    have hbad : ¬ IsGoodAnnulus (μ ω) r z ((1 / 2 : ℝ) ^ (n + 1)) b := mem_iInter.1 hω n
    exact hbad (isGoodAnnulus_mono_mass hgood hsmall.le)
  have hlim := tendsto_measure_iInter_atTop (μ := P)
    (fun n => (hA n).nullMeasurableSet) hanti ⟨0, measure_ne_top P _⟩
  rw [hi] at hlim
  have hδ : 0 < ENNReal.ofReal (1 - p) := ENNReal.ofReal_pos.2 (sub_pos.2 hp.2)
  obtain ⟨n, hn⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_nhds hδ))
  refine ⟨(1 / 2 : ℝ) ^ (n + 1), ⟨by positivity, ?_⟩, (hn n le_rfl).le⟩
  exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)

end HarmonicBalls.Section6
