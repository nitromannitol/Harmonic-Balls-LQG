import HarmonicBalls.Proofs.Sec6.AffineMeasureLaw
import HarmonicBalls.Proofs.Sec6.LQGFineSupportReduction
import HarmonicBalls.Proofs.Sec8.GoodEventMeasurable
import HarmonicBalls.Proofs.Sec8.VeryGoodMeasureScaling

/-! # Affine laws for good annuli

The staged affine field and coordinate-change hypotheses transfer the unit
annulus law to every centre and positive scale. Measurability of the unit
good-annulus event remains an explicit hypothesis.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess
open scoped ENNReal

/-- The affine pullback of a measure has the unit good-annulus property exactly
when the original measure has the corresponding property at the given centre
and scale. -/
theorem isGoodAnnulus_affineMeasure_unit
    {Ω : Type*} (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (a b : ℝ) (ω : Ω) :
    IsGoodAnnulus (affineMeasure γ hcirc μ (r : ℂ) z ω) 1 0 a b ↔
      IsGoodAnnulus (μ ω) r z a b := by
  unfold affineMeasure
  rw [isGoodAnnulus_smul _ _ _ _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
    ENNReal.ofReal_ne_top]
  have hmap : (μ ω).map (fun x : ℂ => (x - z) / (r : ℂ)) =
      ((μ ω).map (fun x : ℂ => x + -z)).map (fun x : ℂ => r⁻¹ • x) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    simp only [Function.comp_apply, Complex.real_smul, sub_eq_add_neg, div_eq_mul_inv,
      Complex.ofReal_inv, mul_comm]
  rw [hmap]
  exact isGoodAnnulus_unit_normalize (μ ω) hr z a b

/-- Under the staged affine laws, the probability of a bad good-annulus event
is independent of its centre and positive radius, provided the unit event is
measurable as a set of measures. -/
theorem badGoodAnnulus_probability_eq_unit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (a b : ℝ) (hmeas : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} =
      P {ω | ¬ IsGoodAnnulus (μ ω) 1 0 a b} := by
  have hd := identDistrib_affineMeasure h hμ hAff hCC hγ hγ2
    (show (r : ℂ) ≠ 0 by exact_mod_cast hr.ne') z
  have heq := hd.measure_mem_eq hmeas.compl
  have hs : {ω | affineMeasure γ hcirc μ (r : ℂ) z ω ∈
      {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}ᶜ} =
      {ω | ¬ IsGoodAnnulus (μ ω) r z a b} := by
    ext ω
    simpa only [mem_ofPred_eq, mem_compl_iff] using
      not_congr (isGoodAnnulus_affineMeasure_unit γ hcirc μ hr z a b ω)
  change P {ω | ¬ IsGoodAnnulus (μ ω) 1 0 a b} =
    P {ω | affineMeasure γ hcirc μ (r : ℂ) z ω ∈
      {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}ᶜ} at heq
  rw [hs] at heq
  exact heq.symm

/-- A positive unit-annulus threshold almost surely yields a deterministic
threshold valid at every centre and positive radius for the same field law. -/
theorem exists_uniform_goodAnnulus_probability_of_ae_unit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (b : ℝ) (hmeas : ∀ n : ℕ, MeasurableSet
      {ν : Measure ℂ | IsGoodAnnulus ν 1 0 ((1 / 2 : ℝ) ^ (n + 1)) b})
    (hae : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (μ ω) 1 0 a b)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ r : ℝ, 0 < r → ∀ z : ℂ,
      P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} ≤ ENNReal.ofReal (1 - p) := by
  let := h.isProbabilityMeasure
  have hμmeas := h.aemeasurable_lqgMeasure hμ
  let ν := hμmeas.mk μ
  have hν : Measurable ν := hμmeas.measurable_mk
  have heq : μ =ᵐ[P] ν := hμmeas.ae_eq_mk
  have hνae : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (ν ω) 1 0 a b := by
    filter_upwards [hae, heq] with ω hω he
    simpa only [← he] using hω
  obtain ⟨a, ha, hbound⟩ := exists_goodAnnulus_threshold_of_measurable_events P
    (μ := ν) (fun n => (hmeas n).preimage hν) hνae hp
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨n, hn⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_nhds ha.1))
  have hsmall : (1 / 2 : ℝ) ^ (n + 1) ≤ a :=
    ((pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)).trans_lt
      (hn n le_rfl)).le
  refine ⟨(1 / 2 : ℝ) ^ (n + 1), ⟨by positivity, ?_⟩, ?_⟩
  · exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  intro r hr z
  rw [badGoodAnnulus_probability_eq_unit hγ hγ2 h hμ hAff hCC _ b (hmeas n) hr z]
  have hm : P {ω | ¬ IsGoodAnnulus (μ ω) 1 0 a b} =
      P {ω | ¬ IsGoodAnnulus (ν ω) 1 0 a b} := by
    apply measure_congr
    filter_upwards [heq] with ω hω
    simp only [hω]
  calc
    P {ω | ¬ IsGoodAnnulus (μ ω) 1 0 ((1 / 2 : ℝ) ^ (n + 1)) b} ≤
        P {ω | ¬ IsGoodAnnulus (μ ω) 1 0 a b} := by
      apply measure_mono
      intro ω hbad hgood
      exact hbad (isGoodAnnulus_mono_mass hgood hsmall)
    _ = P {ω | ¬ IsGoodAnnulus (ν ω) 1 0 a b} := hm
    _ ≤ ENNReal.ofReal (1 - p) := hbound

/-- Local fine support and the unit ball-submean estimate give a threshold
uniform in the centre and positive radius of annuli for a fixed field law. -/
theorem exists_uniform_goodAnnulus_probability_of_ae_local_fine_support
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    {b : ℝ} (hb : 0 < b) (hmeas : ∀ n : ℕ, MeasurableSet
      {ν : Measure ℂ | IsGoodAnnulus ν 1 0 ((1 / 2 : ℝ) ^ (n + 1)) b})
    (hloc : ∀ᵐ ω ∂P, ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
      ∀ E : Set ℂ, MeasurableSet E → (μ ω) (ball x ε \ E) = 0 →
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
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ r : ℝ, 0 < r → ∀ z : ℂ,
      P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} ≤ ENNReal.ofReal (1 - p) := by
  apply exists_uniform_goodAnnulus_probability_of_ae_unit hγ hγ2 h hμ hAff hCC b hmeas
    ?_ hp
  apply ae_exists_goodAnnulus_threshold_of_ae_local_fine_support μ
    (z := 0) (r := 1) (by norm_num) hb ?_ hloc hC0 hCtop hsubmean
  filter_upwards [hμ] with ω hω
  exact hω.isLocallyFiniteMeasure

end HarmonicBalls.Section6
