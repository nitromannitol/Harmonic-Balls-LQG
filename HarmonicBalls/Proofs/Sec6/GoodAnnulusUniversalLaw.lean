import HarmonicBalls.Proofs.Sec6.GoodAnnulusAffineLaw
import HarmonicBalls.Proofs.Sec6.GoodAnnulusReduction
import HarmonicBalls.Proofs.Sec8.LQGUniversalMeasureLaw

/-! # Universality of good-annulus thresholds

A single reference realization supplies a threshold for every realization of
the zero-singularity field. The affine and coordinate-change literature inputs
and the unit-event measurability hypothesis remain explicit.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess
open scoped ENNReal

universe u

/-- A positive unit-annulus threshold for one field realization yields a
threshold uniform over all realizations, centres and positive radii. -/
theorem exists_universal_goodAnnulus_probability_of_ae_unit
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    (hAff₀ : WholePlaneGFFAffineInvariance P₀ hC₀ hcirc₀)
    (hCC₀ : LQGMeasureCoordChange P₀ γ 0 hC₀ hcirc₀)
    (b : ℝ) (hmeas : ∀ n : ℕ, MeasurableSet
      {ν : Measure ℂ | IsGoodAnnulus ν 1 0 ((1 / 2 : ℝ) ^ (n + 1)) b})
    (hae : ∀ᵐ ω ∂P₀, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (μ₀ ω) 1 0 a b)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      WholePlaneGFFAffineInvariance P hC hcirc → LQGMeasureCoordChange P γ 0 hC hcirc →
      ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} ≤ ENNReal.ofReal (1 - p) := by
  obtain ⟨a, ha, hbound⟩ := exists_uniform_goodAnnulus_probability_of_ae_unit
    hγ hγ2 h₀ hμ₀ hAff₀ hCC₀ b hmeas hae hp
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨n, hn⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_nhds ha.1))
  have hsmall : (1 / 2 : ℝ) ^ (n + 1) ≤ a :=
    ((pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)).trans_lt
      (hn n le_rfl)).le
  refine ⟨(1 / 2 : ℝ) ^ (n + 1), ⟨by positivity, ?_⟩, ?_⟩
  · exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  intro Ω _ P hC hcirc μ h hμ hAff hCC r hr z
  rw [badGoodAnnulus_probability_eq_unit hγ hγ2 h hμ hAff hCC _ b (hmeas n) hr z]
  have hd := h₀.identDistrib_lqgMeasure_across_spaces h hμ₀ hμ
  have heq := hd.symm.measure_mem_eq (hmeas n).compl
  change P {ω | ¬ IsGoodAnnulus (μ ω) 1 0 ((1 / 2 : ℝ) ^ (n + 1)) b} =
    P₀ {ω | ¬ IsGoodAnnulus (μ₀ ω) 1 0 ((1 / 2 : ℝ) ^ (n + 1)) b} at heq
  rw [heq]
  calc
    P₀ {ω | ¬ IsGoodAnnulus (μ₀ ω) 1 0 ((1 / 2 : ℝ) ^ (n + 1)) b} ≤
        P₀ {ω | ¬ IsGoodAnnulus (μ₀ ω) 1 0 a b} := by
      apply measure_mono
      intro ω hbad hgood
      exact hbad (isGoodAnnulus_mono_mass hgood hsmall)
    _ ≤ ENNReal.ofReal (1 - p) := hbound 1 (by norm_num) 0

/-- Fine support and the unit submean bound on a single reference realization
suffice for the universal good-annulus probability estimate. -/
theorem exists_universal_goodAnnulus_probability_of_ae_local_fine_support
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    (hAff₀ : WholePlaneGFFAffineInvariance P₀ hC₀ hcirc₀)
    (hCC₀ : LQGMeasureCoordChange P₀ γ 0 hC₀ hcirc₀)
    {b : ℝ} (hb : 0 < b) (hmeas : ∀ n : ℕ, MeasurableSet
      {ν : Measure ℂ | IsGoodAnnulus ν 1 0 ((1 / 2 : ℝ) ^ (n + 1)) b})
    (hloc : ∀ᵐ ω ∂P₀, ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
      ∀ E : Set ℂ, MeasurableSet E → (μ₀ ω) (ball x ε \ E) = 0 →
      ∀ᵐ ω' ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω' = 0)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ∞)
    (hsubmean : ∀ K : Set ℂ, IsCompact K → ∀ u ∈ sphere (0 : ℂ) (4 * 1),
      planarBrownianMotion u
        {ω | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ≤
      C * ∫⁻ x in ball u (1 / 4 : ℝ), planarBrownianMotion x
        {ω | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ∂volume)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      WholePlaneGFFAffineInvariance P hC hcirc → LQGMeasureCoordChange P γ 0 hC hcirc →
      ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} ≤ ENNReal.ofReal (1 - p) := by
  apply exists_universal_goodAnnulus_probability_of_ae_unit hγ hγ2 h₀ hμ₀ hAff₀ hCC₀
    b hmeas ?_ hp
  apply ae_exists_goodAnnulus_threshold_of_ae_local_fine_support μ₀
    (z := 0) (r := 1) (by norm_num) hb ?_ hloc hC0 hCtop hsubmean
  filter_upwards [hμ₀] with ω hω
  exact hω.isLocallyFiniteMeasure

/-- The recurrence and hitting reductions yield an almost-sure positive
unit-annulus threshold under the explicit hitting, zero-one and submean premises. -/
theorem ae_unit_goodAnnulus_threshold_of_hitting_bounds
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
    (hzeroOne : ∀ x : ℂ, ∀ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) → Monotone K →
      0 < planarBrownianMotion x {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω = 0} →
      ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime (⋃ n, K n)ᶜ ω = 0)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ∞)
    (hsubmean : ∀ K : Set ℂ, IsCompact K → ∀ u ∈ sphere (0 : ℂ) (4 * 1),
      planarBrownianMotion u
        {ω | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ≤
      C * ∫⁻ x in ball u (1 / 4 : ℝ), planarBrownianMotion x
        {ω | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ∂volume)
    {b : ℝ} (hb : 0 < b) :
    ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (μ ω) 1 0 a b := by
  let := h.isProbabilityMeasure
  have hloc := ae_ae_lqg_fine_support_of_hitting_bounds hholder hfull hgrowth
    hγ hγ2 h hμ hnonatom hAff hCC hbound hzeroOne
  apply ae_exists_goodAnnulus_threshold_of_ae_local_fine_support μ
    (z := 0) (r := 1) (by norm_num) hb ?_ hloc hC0 hCtop hsubmean
  filter_upwards [hμ] with ω hω
  exact hω.isLocallyFiniteMeasure

/-- The zero-singularity estimate follows from unit-event measurability,
almost-sure positive unit thresholds, and the affine laws. If there is
no realization at the given parameter, the estimate is vacuous. -/
theorem goodAnnulus_zero_probability_of_ae_unit
    (hmeas : ∀ b ∈ Ioo (0 : ℝ) 1, ∀ n : ℕ, MeasurableSet
      {ν : Measure ℂ | IsGoodAnnulus ν 1 0 ((1 / 2 : ℝ) ^ (n + 1)) b})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hunit : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type u) [MeasurableSpace Ω]
      (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc →
      IsLQGMeasureOfField P γ 0 hcirc μ → ∀ b ∈ Ioo (0 : ℝ) 1,
      ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (μ ω) 1 0 a b) :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ b ∈ Ioo (0 : ℝ) 1, ∀ p ∈ Ioo (0 : ℝ) 1, ∃ a ∈ Ioo (0 : ℝ) 1,
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        r / 100 ≤ infDist (0 : ℂ) (annulus z (3 * r) (5 * r)) →
        P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} ≤ ENNReal.ofReal (1 - p) := by
  intro γ hγ hγ2 b hb p hp
  classical
  by_cases hex : ∃ (Ω : Type u) (m : MeasurableSpace Ω), letI := m
      ∃ (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc ∧
          IsLQGMeasureOfField P γ 0 hcirc μ
  · obtain ⟨Ω₀, m₀, P₀, hC₀, hcirc₀, μ₀, h₀, hμ₀⟩ := hex
    let : MeasurableSpace Ω₀ := m₀
    obtain ⟨a, ha, hall⟩ := exists_universal_goodAnnulus_probability_of_ae_unit
      hγ hγ2 h₀ hμ₀ (hAff Ω₀ P₀ hC₀ hcirc₀) (hCC Ω₀ P₀ γ hC₀ hcirc₀)
      b (hmeas b hb) (hunit γ hγ hγ2 Ω₀ P₀ hC₀ hcirc₀ μ₀ h₀ hμ₀ b hb) hp
    refine ⟨a, ha, ?_⟩
    intro Ω _ P hC hcirc μ h hμ r hr z _
    exact hall Ω P hC hcirc μ h hμ (hAff Ω P hC hcirc) (hCC Ω P γ hC hcirc) r hr z
  · refine ⟨1 / 2, by norm_num, ?_⟩
    intro Ω m P hC hcirc μ h hμ r hr z hd
    exact False.elim (hex ⟨Ω, m, P, hC, hcirc, μ, h, hμ⟩)

/-- Lemma 6.4 follows from the unit-annulus premises and the explicit
LQG existence, coordinate-change, affine-invariance and Weyl-scaling inputs. -/
theorem goodAnnulusProbabilityStmt_of_ae_unit
    (hmeas : ∀ b ∈ Ioo (0 : ℝ) 1, ∀ n : ℕ, MeasurableSet
      {ν : Measure ℂ | IsGoodAnnulus ν 1 0 ((1 / 2 : ℝ) ^ (n + 1)) b})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hunit : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type u) [MeasurableSpace Ω]
      (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc →
      IsLQGMeasureOfField P γ 0 hcirc μ → ∀ b ∈ Ioo (0 : ℝ) 1,
      ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (μ ω) 1 0 a b)
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureWeylScaling P γ 0 hC hcirc) : GoodAnnulusProbabilityStmt.{u} := by
  exact goodAnnulusProbabilityStmt_of_zero
    (goodAnnulus_zero_probability_of_ae_unit hmeas hAff hCC hunit) hex hW

end HarmonicBalls.Section6
