import HarmonicBalls.Proofs.Sec6.SingularRootPolynomialOrigin
import HarmonicBalls.Proofs.Sec6.UnitDiscRootedDyadicPrevalence
import HarmonicBalls.Proofs.Sec6.PrevalenceGridUnion

/-! # Singular-mass-typical dyadic annulus counts

The countable-centre iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

/-- A singular-mass sampled root has many singular-measure good annuli in
all sufficiently small dyadic windows, at each prescribed physical scale. -/
theorem exists_ae_singular_unitDisc_root_eventually_dyadic_goodAnnuli_count
    (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      ∀ᵐ p ∂(P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const),
      ∀ i, ∀ᶠ n : ℕ in atTop,
        (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus (μ p.1) (s i * r) p.2
            (a / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) (b + 1)}.ncard : ℝ) := by
  obtain ⟨q, hq, a, ha, htail⟩ :=
    exists_singular_unitDisc_root_goodAnnuli_polynomial_tail hball hγ hγ2 hα h hμ hμ₀ hb β hβ
  refine ⟨a, ha, ae_all_iff.mpr ?_⟩
  intro i
  obtain ⟨C, hC, ε₀, hε₀, htail⟩ := htail (s i) (hs i)
  obtain ⟨δ, hδ, hlog⟩ := exists_radius_logb_inverse_ge (b := 7) (D := 16) (by norm_num)
  let Q := P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
    (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const
  let E : ℝ → Set (Ω × ℂ) := fun ε => {p |
    (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
      ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
        IsGoodAnnulus (μ p.1) (s i * r) p.2
          (a / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) (b + 1)}.ncard : ℝ)}
  have hpoly : PolyHighProb Q E := by
    refine ⟨q, hq, C, min ε₀ δ, lt_min hε₀ hδ, ?_⟩
    intro ε hε hε'
    have hh := htail ε hε (hε'.trans_le (min_le_left _ _))
      (hlog ε hε (hε'.trans_le (min_le_right _ _)))
    simpa only [Q, E, Set.compl_ofPred, not_le] using hh
  simpa only [Q, E, dyadicScale, mem_ofPred_eq] using hpoly.ae_eventually_dyadic

/-- The normalized singular-root almost-sure count passes to singular mass
restricted to the unit disk for almost every field. -/
theorem exists_ae_singular_mass_eventually_dyadic_goodAnnuli_count
    (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P,
      ∀ᵐ z ∂(μ ω).restrict (ball 0 1), ∀ i, ∀ᶠ n : ℕ in atTop,
        (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus (μ ω) (s i * r) z
            (a / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) (b + 1)}.ncard : ℝ) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  obtain ⟨a, ha, ht⟩ := exists_ae_singular_unitDisc_root_eventually_dyadic_goodAnnuli_count
    hball hγ hγ2 hα h hμ hμ₀ hb β hβ s hs
  refine ⟨a, ha, ?_⟩
  have hsection := Measure.ae_ae_of_ae_compProd ht
  filter_upwards [hsection, hμ,
    ae_weightedRestrictionKernel_eq P μ (h.aemeasurable_lqgMeasure hμ)
      (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const] with ω hh hloc he
  let : IsLocallyFiniteMeasure (μ ω) := hloc.isLocallyFiniteMeasure
  have hfin : μ ω (ball 0 1) ≠ ∞ := measure_ball_ne_top
  rw [he, normalizedRestriction, withDensity_const, one_smul] at hh
  exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr hfin)).mp hh

/-- The staged zero-strength existence input provides the comparison measure
for the singular-mass-typical count. -/
theorem exists_ae_singular_mass_eventually_dyadic_goodAnnuli_count_of_existence
    (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hE₀ : LQGMeasureExistence P γ 0 hC hcirc)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P,
      ∀ᵐ z ∂(μ ω).restrict (ball 0 1), ∀ i, ∀ᶠ n : ℕ in atTop,
        (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus (μ ω) (s i * r) z
            (a / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) (b + 1)}.ncard : ℝ) := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := hE₀ h hγ hγ2 hQ
  exact exists_ae_singular_mass_eventually_dyadic_goodAnnuli_count
    hball hγ hγ2 hα h hμ hμ₀ hb β hβ s hs

end HarmonicBalls.Section6
