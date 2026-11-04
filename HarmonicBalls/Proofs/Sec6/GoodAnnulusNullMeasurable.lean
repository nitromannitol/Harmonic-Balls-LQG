import HarmonicBalls.Proofs.Sec6.GoodAnnulusThreshold
import HarmonicBalls.Proofs.Sec6.LQGFineSupportZeroOne
import HarmonicBalls.Proofs.Sec8.LQGRandomGoodAnnulus

/-! # Good-annulus thresholds from measurable versions

A Borel representative up to a null set suffices to choose a deterministic
mass threshold. For LQG measures, the Section 8 representative applies under
explicit point avoidance, full support, and nonatomicity hypotheses.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter Topology MarkovProcess ProbabilityTheory
open scoped ENNReal NNReal

/-- Null measurability of the dyadic good events suffices for a deterministic
positive threshold. -/
theorem exists_goodAnnulus_threshold_of_nullMeasurable_events
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {μ : Ω → Measure ℂ} {r b : ℝ} {z : ℂ}
    (hmeas : ∀ n : ℕ, NullMeasurableSet
      {ω | IsGoodAnnulus (μ ω) r z ((1 / 2 : ℝ) ^ (n + 1)) b} P)
    (hae : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (μ ω) r z a b)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} ≤ ENNReal.ofReal (1 - p) := by
  let A : ℕ → Set Ω := fun n => {ω | ¬ IsGoodAnnulus (μ ω) r z ((1 / 2 : ℝ) ^ (n + 1)) b}
  have hA : ∀ n, NullMeasurableSet (A n) P := fun n => (hmeas n).compl
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
    (fun n => hA n) hanti ⟨0, measure_ne_top P _⟩
  rw [hi] at hlim
  have hδ : 0 < ENNReal.ofReal (1 - p) := ENNReal.ofReal_pos.2 (sub_pos.2 hp.2)
  obtain ⟨n, hn⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_nhds hδ))
  refine ⟨(1 / 2 : ℝ) ^ (n + 1), ⟨by positivity, ?_⟩, (hn n le_rfl).le⟩
  exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)


universe u

/-- The Section 8 measurable versions yield a deterministic threshold for a
reference LQG field, conditional on Brownian point avoidance and an almost-sure
positive random threshold. -/
theorem exists_lqg_goodAnnulus_threshold_of_ae_point_avoidance
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hatom : LQGMeasureNonatomic P γ α₀ hC hcirc)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (b : ℝ)
    (hpolar : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    (hae : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (μ ω) r z a b)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} ≤ ENNReal.ofReal (1 - p) := by
  let := hGFF.isProbabilityMeasure
  apply exists_goodAnnulus_threshold_of_nullMeasurable_events P ?_ hae hp
  intro n
  obtain ⟨A, hA, hrep⟩ := exists_measurable_lqg_isGoodAnnulus_of_ae_point_avoidance
    hfull P γ α₀ hγ hγ2 hα hC hcirc μ hGFF hμ hatom r hr z
    ((1 / 2 : ℝ) ^ (n + 1)) b (by positivity) hpolar
  apply hA.nullMeasurableSet.congr
  filter_upwards [hrep] with ω hω
  exact propext hω

/-- Equal laws of random measures give equal good-annulus probabilities when
a single Borel representative applies almost surely to both random measures. -/
theorem badGoodAnnulus_probability_eq_of_identDistrib_of_regular
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {μ : Ω → Measure ℂ} {μ' : Ω' → Measure ℂ}
    (hd : IdentDistrib μ μ' P P') {r : ℝ} (hr : 0 < r) (z : ℂ) (a b : ℝ)
    (hsmall : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε)
    (hreg : ∀ᵐ ω ∂P, (∀ x : ℂ, μ ω {x} = 0) ∧
      μ ω (annulus z (3 * r) (5 * r)) ≠ ∞ ∧
      0 < ENNReal.ofReal a * μ ω (annulus z (3 * r) (5 * r)))
    (hreg' : ∀ᵐ ω ∂P', (∀ x : ℂ, μ' ω {x} = 0) ∧
      μ' ω (annulus z (3 * r) (5 * r)) ≠ ∞ ∧
      0 < ENNReal.ofReal a * μ' ω (annulus z (3 * r) (5 * r))) :
    P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} =
      P' {ω | ¬ IsGoodAnnulus (μ' ω) r z a b} := by
  obtain ⟨G, hG, hrep⟩ := exists_measurable_isGoodAnnulus_on_atomless r hr z a b hsmall
  have hleft : P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} = P {ω | μ ω ∈ Gᶜ} := by
    apply measure_congr
    filter_upwards [hreg] with ω hω
    simp only [mem_compl_iff]
    exact propext (not_congr (hrep (μ ω) ⟨hω.1⟩ hω.2.1 hω.2.2)).symm
  have hright : P' {ω | ¬ IsGoodAnnulus (μ' ω) r z a b} = P' {ω | μ' ω ∈ Gᶜ} := by
    apply measure_congr
    filter_upwards [hreg'] with ω hω
    simp only [mem_compl_iff]
    exact propext (not_congr (hrep (μ' ω) ⟨hω.1⟩ hω.2.1 hω.2.2)).symm
  rw [hleft, hright]
  exact hd.measure_mem_eq hG.compl

/-- The hitting and ball-submean reductions give a deterministic unit-annulus
threshold without assuming the good event itself is Borel measurable. -/
theorem exists_unit_goodAnnulus_threshold_of_hitting_bounds_and_point_avoidance
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hnonatom : LQGMeasureNonatomic P γ 0 hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hbound : ∀ᵐ ω ∂P, ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
      ∀ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) → Monotone K →
      (μ ω) (ball x ε \ ⋃ n, K n) = 0 →
      ∀ᶠ n in atTop,
        ENNReal.ofReal (greenPotentialExtremaRatio (fineSupportAnnulus x (fineSupportScale n))
          (sphere x (fineSupportScale n / 4)) (μ ω)) ≤ planarBrownianMotion x
        {ω' | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω' ≤
          ContinuousPath.exitTime (ball x (fineSupportScale n)) ω'})
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ∞)
    (hsubmean : ∀ K : Set ℂ, IsCompact K → ∀ u ∈ sphere (0 : ℂ) (4 * 1),
      planarBrownianMotion u
        {ω | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ≤
      C * ∫⁻ x in ball u (1 / 4 : ℝ), planarBrownianMotion x
        {ω | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ∂volume)
    (hpolar : ∀ u ∈ sphere (0 : ℂ) (4 * 1),
      ∀ x ∈ annulus 0 (3 * 1) (5 * 1), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    {b : ℝ} (hb : 0 < b) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      P {ω | ¬ IsGoodAnnulus (μ ω) 1 0 a b} ≤ ENNReal.ofReal (1 - p) := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  apply exists_lqg_goodAnnulus_threshold_of_ae_point_avoidance hfull hγ hγ2 hQ
    h hμ hnonatom (by norm_num) 0 b hpolar ?_ hp
  exact ae_unit_goodAnnulus_threshold_of_hitting_bounds_zeroOne hholder hfull hgrowth
    hγ hγ2 h hμ hnonatom hAff hCC hbound hC0 hCtop hsubmean hb

end HarmonicBalls.Section6
