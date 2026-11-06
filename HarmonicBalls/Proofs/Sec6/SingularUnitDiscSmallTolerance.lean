import HarmonicBalls.Proofs.Sec6.RootedLocalSmallTolerance
import HarmonicBalls.Proofs.Sec6.SingularRootPolynomialOrigin

/-! # Polynomial tails for small avoidance tolerances

The annulus counts use Leonardo Bonanno’s iteration in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

/-- A finite cover inherits the small-tolerance rooted annulus count tail. -/
theorem exists_rooted_finiteCover_goodAnnuli_count_tail_smallTolerance
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ (κ : Kernel Ω ℂ) [IsSFiniteKernel κ],
      (∀ᵐ ω ∂P, κ ω univ = 1) → (∀ᵐ ω ∂P, κ ω ≪ μ ω) →
    ∀ (T : Finset ℂ) (s ε : ℝ), 0 < s → 0 < ε →
      16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      (P ⊗ₘ κ) {p | (∃ x ∈ T, p.2 ∈ ball x (s * ε / 100)) ∧
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2 a b}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤
      (T.card : ℝ≥0∞) * ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) := by
  classical
  obtain ⟨a, ha, C, hC, hlocal⟩ :=
    exists_rooted_local_goodAnnuli_count_tail_smallTolerance hgrowth hγ hγ2 h hμ hb α β hα hβ
  refine ⟨a, ha, C, hC, ?_⟩
  intro κ _ hκ hac T s ε hs hε ht
  let E : ℂ → Set (Ω × ℂ) := fun x => {p | p.2 ∈ ball x (s * ε / 100) ∧
    ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
      IsGoodAnnulus (μ p.1) (s * r) p.2 a b}.ncard : ℝ) <
      (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))}
  calc
    _ ≤ (P ⊗ₘ κ) (⋃ x ∈ T, E x) := by
      apply measure_mono
      intro p hp
      obtain ⟨⟨x, hx, hpx⟩, hbad⟩ := hp
      exact mem_iUnion₂.mpr ⟨x, hx, hpx, hbad⟩
    _ ≤ ∑ x ∈ T, (P ⊗ₘ κ) (E x) := measure_biUnion_finset_le T E
    _ ≤ ∑ _x ∈ T, ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) := by
      apply Finset.sum_le_sum
      intro x hx
      exact hlocal κ hκ hac x s ε hs hε ht
    _ = _ := by simp


/-- A unit-disc cover gives a rooted count tail with a geometric prefactor. -/
theorem exists_rooted_unitDisc_goodAnnuli_count_tail_smallTolerance
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ (κ : Kernel Ω ℂ) [IsSFiniteKernel κ],
      (∀ᵐ ω ∂P, κ ω univ = 1) → (∀ᵐ ω ∂P, κ ω ≪ μ ω) →
    ∀ (s ε : ℝ), 0 < s → 0 < ε → ε ≤ 1 →
      16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      (P ⊗ₘ κ) {p | p.2 ∈ ball (0 : ℂ) 1 ∧
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2 a b}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤
      ENNReal.ofReal ((2800 / (min s 1 * ε)) ^ 2) *
        ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) := by
  classical
  obtain ⟨a, ha, C, hC, htail⟩ :=
    exists_rooted_finiteCover_goodAnnuli_count_tail_smallTolerance hgrowth hγ hγ2 h hμ hb α β hα hβ
  refine ⟨a, ha, C, hC, ?_⟩
  intro κ _ hκ hac s ε hs hε hε1 ht
  let δ : ℝ := min s 1 * ε / 400
  have hmin : 0 < min s 1 := lt_min hs (by norm_num)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    have hm : min s 1 ≤ 1 := min_le_right _ _
    have hprod : min s 1 * ε ≤ 1 := by nlinarith
    dsimp [δ]; linarith
  obtain ⟨T, hcard, hcover⟩ := exists_unitDisc_lattice_cover hδ hδ1
  have hbound : 2 * δ < s * ε / 100 := by
    have hm : min s 1 ≤ s := min_le_left _ _
    have hmul : min s 1 * ε ≤ s * ε := mul_le_mul_of_nonneg_right hm hε.le
    have hpos : 0 < s * ε := mul_pos hs hε
    dsimp [δ]; linarith
  have hc : (T.card : ℝ≥0∞) ≤ ENNReal.ofReal ((2800 / (min s 1 * ε)) ^ 2) := by
    have heq : 7 / δ = 2800 / (min s 1 * ε) := by dsimp [δ]; ring
    rw [heq] at hcard
    exact_mod_cast (ENNReal.ofReal_le_ofReal hcard)
  calc
    _ ≤ (P ⊗ₘ κ) {p | (∃ x ∈ T, p.2 ∈ ball x (s * ε / 100)) ∧
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2 a b}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} := by
      apply measure_mono
      intro p hp
      obtain ⟨x, hx, hpx⟩ := hcover p.2 hp.1
      exact ⟨⟨x, hx, ball_subset_ball hbound.le hpx⟩, hp.2⟩
    _ ≤ (T.card : ℝ≥0∞) * ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) :=
      htail κ hκ hac T s ε hs hε ht
    _ ≤ _ := by gcongr


/-- Arbitrarily high input tail exponents absorb the unit-disc covering cost. -/
theorem exists_rooted_unitDisc_goodAnnuli_polynomial_tail_smallTolerance
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (q β : ℝ) (hq : 0 < q) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ, 0 < s → ∃ C : ℝ, 0 < C ∧
    ∀ (κ : Kernel Ω ℂ) [IsSFiniteKernel κ],
      (∀ᵐ ω ∂P, κ ω univ = 1) → (∀ᵐ ω ∂P, κ ω ≪ μ ω) →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      (P ⊗ₘ κ) {p | p.2 ∈ ball (0 : ℂ) 1 ∧
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2 a b}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤ ENNReal.ofReal (C * ε ^ q) := by
  have hl : 0 < Real.log 7 := Real.log_pos (by norm_num)
  obtain ⟨a, ha, C, hC, ht⟩ := exists_rooted_unitDisc_goodAnnuli_count_tail_smallTolerance
    hgrowth hγ hγ2 h hμ hb (16 * Real.log 7 * (q + 2)) β (by positivity) hβ
  refine ⟨a, ha, ?_⟩
  intro s hs
  have hm : 0 < min s 1 := lt_min hs (by norm_num)
  refine ⟨(2800 / min s 1) ^ 2 * C, by positivity, ?_⟩
  intro κ _ hk hac ε hε hε1 hlog
  have he : 16 * Real.log 7 * (q + 2) / (16 * Real.log 7) = q + 2 := by
    field_simp
  have hpow : ε ^ (q + 2) = ε ^ q * ε ^ (2 : ℕ) := by
    rw [Real.rpow_add hε, Real.rpow_two]
  have hid : (2800 / (min s 1 * ε)) ^ 2 * (C * ε ^ (q + 2)) =
      ((2800 / min s 1) ^ 2 * C) * ε ^ q := by
    rw [hpow]
    field_simp
  calc
    _ ≤ ENNReal.ofReal ((2800 / (min s 1 * ε)) ^ 2) *
        ENNReal.ofReal (C * ε ^ (q + 2)) := by simpa only [he] using ht κ hk hac s ε hs hε hε1 hlog
    _ = _ := by rw [← ENNReal.ofReal_mul (sq_nonneg _), hid]


/-- A singular-mass root has a polynomial count tail for zero-strength annuli. -/
theorem exists_singular_unitDisc_root_zero_goodAnnuli_polynomial_tail_smallTolerance
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    {b : ℝ} (hb : 0 < b) (q β : ℝ) (hq : 0 < q) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ, 0 < s → ∃ C : ℝ, 0 < C ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        {p | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ₀ p.1) (s * r) p.2 a b}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤ ENNReal.ofReal (C * ε ^ q) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  let hm := h.aemeasurable_lqgMeasure hμ
  let κ := weightedRestrictionKernel P μ hm (ball 0 1) measurableSet_ball
    (fun _ => 1) measurable_const
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ α hγ hγ2 hα
    Ω P hC hcirc μ h hμ
  have hmass : ∀ᵐ ω ∂P, ((μ ω).withDensity (fun _ => 1)) (ball 0 1) ≠ 0 ∧
      ((μ ω).withDensity (fun _ => 1)) (ball 0 1) ≠ ∞ := by
    filter_upwards [hfull, hμ] with ω hf hloc
    let : IsLocallyFiniteMeasure (μ ω) := hloc.isLocallyFiniteMeasure
    simpa only [withDensity_const, one_smul] using
      (show μ ω (ball 0 1) ≠ 0 ∧ μ ω (ball 0 1) ≠ ∞ from
        ⟨(hf _ isOpen_ball ⟨0, mem_ball_self (by norm_num)⟩).ne', measure_ball_ne_top⟩)
  have hk : ∀ᵐ ω ∂P, κ ω univ = 1 := by
    filter_upwards [ae_weightedRestrictionKernel_eq P μ hm (ball 0 1) measurableSet_ball
      (fun _ => 1) measurable_const, hmass] with ω he hh
    rw [he]
    simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hh.1 hh.2
  have hac : ∀ᵐ ω ∂P, κ ω ≪ μ₀ ω := by
    filter_upwards [ae_weightedRestrictionKernel_eq P μ hm (ball 0 1) measurableSet_ball
      (fun _ => 1) measurable_const,
      ae_singular_lqg_absolutelyContinuous_zero hgrowth hγ hγ2 hα h hμ hμ₀] with ω he hμν
    rw [he, normalizedRestriction]
    exact Measure.smul_absolutelyContinuous.trans
      (Measure.absolutelyContinuous_restrict.trans
        ((withDensity_absolutelyContinuous _ _).trans hμν))
  obtain ⟨a, ha, ht⟩ := exists_rooted_unitDisc_goodAnnuli_polynomial_tail_smallTolerance
    hgrowth hγ hγ2 h hμ₀ hb q β hq hβ
  refine ⟨a, ha, ?_⟩
  intro s hs
  obtain ⟨C, hC, htail⟩ := ht s hs
  refine ⟨C, hC, ?_⟩
  intro ε hε hε1 hlog
  calc
    _ ≤ (P ⊗ₘ κ) {p | p.2 ∈ ball (0 : ℂ) 1 ∧
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ₀ p.1) (s * r) p.2 a b}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} := by
      apply measure_mono_ae
      filter_upwards [ae_mem_weightedRestriction_compProd P μ hm (ball 0 1)
        measurableSet_ball (fun _ => 1) measurable_const] with p hp hpE
      exact ⟨hp, hpE⟩
    _ ≤ _ := htail κ hk hac ε hε hε1 hlog


/-- Separated singular roots have a polynomial count tail for singular annuli. -/
theorem exists_singular_unitDisc_root_separated_goodAnnuli_polynomial_tail_smallTolerance
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    {b : ℝ} (hb : 0 < b) (q β : ℝ) (hq : 0 < q) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ, 0 < s → ∃ C : ℝ, 0 < C ∧
    ∀ ε t : ℝ, 0 < ε → ε ≤ 1 → 16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      6 * s * ε ^ (3 / 4 : ℝ) ≤ t →
      (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        {p | t ≤ ‖p.2‖ ∧
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus (μ p.1) (s * r) p.2
              (a / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) b}.ncard : ℝ) <
          (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤ ENNReal.ofReal (C * ε ^ q) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  obtain ⟨a, ha, ht⟩ := exists_singular_unitDisc_root_zero_goodAnnuli_polynomial_tail_smallTolerance
    hgrowth hγ hγ2 hα h hμ hμ₀ hb q β hq hβ
  refine ⟨a, ha, ?_⟩
  intro s hs
  obtain ⟨C, hC, htail⟩ := ht s hs
  refine ⟨C, hC, ?_⟩
  intro ε t hε hε1 hlog hsmall
  let κ := weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
    (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const
  have hweight := (quasiMeasurePreserving_fst_compProd P κ).ae
    (ae_singular_lqg_eq_power_weight hgrowth hγ hγ2 hα h hμ hμ₀)
  apply (measure_mono_ae ?_).trans (htail ε hε hε1 hlog)
  filter_upwards [hweight] with p hp hw
  obtain ⟨hroot, hbad⟩ := hw
  have hfinite : {r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
      IsGoodAnnulus (μ p.1) (s * r) p.2
        (a / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) b}.Finite := by
    apply finite_of_geometric (q := (7 : ℝ)⁻¹) (A := 1) (lo := ε)
      (by norm_num) (by norm_num) hε
    intro r hr
    obtain ⟨n, hn⟩ := hr.2.1
    exact ⟨hr.1.1, n, by simpa using hn⟩
  have hcount : ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
      IsGoodAnnulus (μ₀ p.1) (s * r) p.2 a b}.ncard : ℝ) ≤
    ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
      IsGoodAnnulus (μ p.1) (s * r) p.2
        (a / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) b}.ncard : ℝ) := by
    norm_cast
    apply Set.ncard_le_ncard ?_ hfinite
    intro r hr
    refine ⟨hr.1, hr.2.1, ?_⟩
    have hrpos : 0 < s*r := mul_pos hs (hε.trans_le hr.1.1)
    have hsep : 6 * (s*r) ≤ ‖p.2‖ := by
      calc
        _ ≤ 6 * s * ε ^ (3 / 4 : ℝ) := by nlinarith [hr.1.2]
        _ ≤ t := hsmall
        _ ≤ _ := hroot
    apply isGoodAnnulus_of_singular_weight hrpos
      (annulus_separated_of_six_mul_le_norm hrpos hsep) ?_ hr.2.2
    rw [hp]
  exact lt_of_le_of_lt hcount hbad


/-- The singular-root origin bound removes the separation restriction. -/
theorem exists_singular_unitDisc_root_goodAnnuli_polynomial_tail_smallTolerance
    (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ q : ℝ, 0 < q ∧ ∃ a ∈ Ioo (0 : ℝ) 1,
    ∀ s : ℝ, 0 < s → ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → 16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        {p | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2
            (a / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) b}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤ ENNReal.ofReal (C * ε ^ q) := by
  let hgrowth := lqgVolumeGrowthAllScalesStmt_of_ballMass hball
  obtain ⟨k, hk, D, hD, t₀, ht₀, hnear⟩ :=
    exists_singular_unitDisc_root_origin_polynomial_bound hball hγ hγ2 hα h hμ
  have hq : 0 < (3 / 4 : ℝ) * k := mul_pos (by norm_num) hk
  obtain ⟨a, ha, htail⟩ := exists_singular_unitDisc_root_separated_goodAnnuli_polynomial_tail_smallTolerance
    hgrowth hγ hγ2 hα h hμ hμ₀ hb ((3 / 4 : ℝ) * k) β hq hβ
  refine ⟨_, hq, a, ha, ?_⟩
  intro s hs
  obtain ⟨C, hC, htail⟩ := htail s hs
  obtain ⟨ε₁, hε₁, hsmall⟩ := exists_pos_forall_rpow_le
    (a := (3 / 4 : ℝ)) (c := t₀ / (12 * s)) (by norm_num) (by positivity)
  refine ⟨C + D * (6 * s) ^ k, by positivity, min ε₁ 1, lt_min hε₁ one_pos, ?_⟩
  intro ε hε hε₀ hlog
  have hε1 : ε ≤ 1 := (hε₀.trans_le (min_le_right _ _)).le
  have hscale : 0 < 6 * s * ε ^ (3 / 4 : ℝ) := by positivity
  have hscale' : 6 * s * ε ^ (3 / 4 : ℝ) < t₀ := by
    have hh := hsmall ε hε (hε₀.trans_le (min_le_left _ _))
    have hs' : 0 < 12 * s := by positivity
    have hh' := (le_div_iff₀ hs').mp hh
    nlinarith
  have hn := hnear (6 * s * ε ^ (3 / 4 : ℝ)) hscale hscale'
  have hn' : (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        {p | ‖p.2‖ < 6 * s * ε ^ (3 / 4 : ℝ)} ≤
      ENNReal.ofReal (D * (6 * s) ^ k * ε ^ ((3 / 4 : ℝ) * k)) := by
    have heq : (univ ×ˢ ball (0 : ℂ) (6 * s * ε ^ (3 / 4 : ℝ))) =
        {p : Ω × ℂ | ‖p.2‖ < 6 * s * ε ^ (3 / 4 : ℝ)} := by
      ext p
      simp only [mem_prod, mem_univ, true_and, mem_ball, dist_zero_right, mem_ofPred_eq]
    rw [heq] at hn
    convert hn using 1
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hε.le _),
      ← Real.rpow_mul hε.le]
    ring_nf
  calc
    _ ≤ (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        {p | ‖p.2‖ < 6 * s * ε ^ (3 / 4 : ℝ)} +
      (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        {p | 6 * s * ε ^ (3 / 4 : ℝ) ≤ ‖p.2‖ ∧
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus (μ p.1) (s * r) p.2
              (a / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) b}.ncard : ℝ) <
          (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} := by
      apply (measure_mono ?_).trans (measure_union_le _ _)
      intro p hp
      by_cases hz : ‖p.2‖ < 6 * s * ε ^ (3 / 4 : ℝ)
      · exact Or.inl hz
      · exact Or.inr ⟨le_of_not_gt hz, hp⟩
    _ ≤ ENNReal.ofReal (D * (6 * s) ^ k * ε ^ ((3 / 4 : ℝ) * k)) +
      ENNReal.ofReal (C * ε ^ ((3 / 4 : ℝ) * k)) :=
        add_le_add hn' (htail ε _ hε hε1 hlog le_rfl)
    _ = ENNReal.ofReal ((C + D * (6 * s) ^ k) * ε ^ ((3 / 4 : ℝ) * k)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring


end HarmonicBalls.Section6
