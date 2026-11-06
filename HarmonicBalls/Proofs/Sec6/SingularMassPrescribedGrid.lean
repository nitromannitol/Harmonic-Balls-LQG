import HarmonicBalls.Proofs.Sec6.SingularRootBoundedFineGrid

/-! # Prescribed-grid counts at singular-mass-typical centres

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

/-- Scaling a common seven-adic subrange count preserves the common radii
and gives the physical window and positive indices of criterion three. -/
theorem scaled_common_criterionThree_count_of_sqrt
    {μ : Measure ℂ} {a₁ a₂ b₁ b₂ c s : ℝ} (hs : 0 < s)
    {n : ℕ} (hn : 9 ≤ n) {z w : ℂ}
    (h : c * Real.logb 7 ((dyadicScale n) ^ (-(1 / 2 : ℝ))) ≤
      ({r : ℝ | r ∈ Icc (dyadicScale n) (Real.sqrt (dyadicScale n)) ∧
        (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
        IsGoodAnnulus μ (s*r) z a₁ b₁ ∧ IsGoodAnnulus μ (s*r) w a₂ b₂}.ncard : ℝ)) :
    c * Real.logb 7 ((dyadicScale n) ^ (-(1 / 2 : ℝ))) ≤
      ({r : ℝ | r ∈ Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = s * (7 : ℝ)⁻¹ ^ k) ∧
        IsGoodAnnulus μ r z a₁ b₁ ∧ IsGoodAnnulus μ r w a₂ b₂}.ncard : ℝ) := by
  let ε := dyadicScale n
  have hε : 0 < ε := dyadicScale_pos n
  have hsqrt := sqrt_dyadicScale_le_one_twentieth hn
  let T : Set ℝ := {r | r ∈ Icc ε (Real.sqrt ε) ∧
    (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
    IsGoodAnnulus μ (s*r) z a₁ b₁ ∧ IsGoodAnnulus μ (s*r) w a₂ b₂}
  let U : Set ℝ := {r | r ∈ Icc (ε*s) (Real.sqrt ε*s) ∧
    (∃ k : ℕ, 1 ≤ k ∧ r = s * (7 : ℝ)⁻¹ ^ k) ∧
    IsGoodAnnulus μ r z a₁ b₁ ∧ IsGoodAnnulus μ r w a₂ b₂}
  have hfin : U.Finite := by
    refine finite_of_geometric (q := (7 : ℝ)⁻¹) (A := s) (lo := ε*s)
      (by norm_num) (by norm_num) (mul_pos hε hs) fun r hr => ⟨hr.1.1, ?_⟩
    obtain ⟨k, _, hk⟩ := hr.2.1
    exact ⟨k, hk⟩
  have hinj : Function.Injective (fun r : ℝ => s*r) := by
    intro x y hxy
    exact mul_left_cancel₀ hs.ne' hxy
  have hsub : (fun r : ℝ => s*r) '' T ⊆ U := by
    rintro r ⟨t, ht, rfl⟩
    have ht_sqrt : t ≤ Real.sqrt ε := ht.1.2
    obtain ⟨k, hk⟩ := ht.2.1
    have hk1 : 1 ≤ k := by
      by_contra hbad
      have : k = 0 := by omega
      subst k
      simp only [pow_zero] at hk
      have : Real.sqrt ε ≤ (1 / 20 : ℝ) := hsqrt
      linarith
    refine ⟨⟨?_, ?_⟩, ⟨k, hk1, by rw [hk]⟩, ht.2.2⟩
    · nlinarith [mul_le_mul_of_nonneg_left ht.1.1 hs.le]
    · nlinarith [mul_le_mul_of_nonneg_left ht_sqrt hs.le]
  have hcard : T.ncard ≤ U.ncard := by
    calc
      T.ncard = ((fun r : ℝ => s*r) '' T).ncard := hinj.injOn.ncard_image.symm
      _ ≤ U.ncard := Set.ncard_le_ncard hsub hfin
  exact h.trans (by exact_mod_cast hcard)


/-- For a countable family of physical scales, singular-mass-typical centres
and a nearby prescribed-grid centre share many good radii eventually along dyadic
windows. The displacement constant may depend on the physical scale. -/
theorem exists_ae_singular_mass_common_goodAnnulus_prescribedGrid_dyadic
    (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧
      ∃ C : ℕ → ℝ, (∀ i, 1 ≤ C i) ∧
      ∀ᵐ ω ∂P, ∀ᵐ w ∂(μ ω).restrict (ball 0 1),
        ∀ i, ∀ᶠ n : ℕ in atTop,
          ∃ z ∈ prevalenceGrid (dyadicScale n),
            dist w z < δ * (s i * (C i * dyadicScale n)) ∧
            (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-(1 / 2 : ℝ))) ≤
              ({r : ℝ | r ∈ Icc (dyadicScale n) (Real.sqrt (dyadicScale n)) ∧
                (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
                IsGoodAnnulus (μ ω) (s i*r) z
                  (a / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) (b/2) ∧
                IsGoodAnnulus (μ ω) (s i*r) w
                  ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b}.ncard : ℝ) := by
  classical
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  obtain ⟨a, ha, δ, hδ, ht⟩ := exists_singular_root_common_goodAnnulus_prescribedGrid
    hball h hμ hμ₀ hAff hCC hγ hγ2 hα hb β hβ
  have hc : ∀ i, ∃ C : ℝ, 1 ≤ C ∧ PolyHighProb
      (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
      (fun ε => {p | ∃ z ∈ prevalenceGrid ε,
        dist p.2 z < δ * (s i*(C*ε)) ∧
        (β / 16) * Real.logb 7 (ε ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc ε (Real.sqrt ε) ∧
            (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
            IsGoodAnnulus (μ p.1) (s i*r) z
              (a / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) (b/2) ∧
            IsGoodAnnulus (μ p.1) (s i*r) p.2
              ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b}.ncard : ℝ)}) :=
    fun i => ht (s i) (hs i)
  choose C hC hprob using hc
  refine ⟨a, ha, δ, hδ, C, hC, ?_⟩
  have hall : ∀ᵐ p ∂(P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
      (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const),
      ∀ i, ∀ᶠ n : ℕ in atTop,
        ∃ z ∈ prevalenceGrid (dyadicScale n),
          dist p.2 z < δ * (s i * (C i * dyadicScale n)) ∧
          (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-(1 / 2 : ℝ))) ≤
            ({r : ℝ | r ∈ Icc (dyadicScale n) (Real.sqrt (dyadicScale n)) ∧
              (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus (μ p.1) (s i*r) z
                (a / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) (b/2) ∧
              IsGoodAnnulus (μ p.1) (s i*r) p.2
                ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b}.ncard : ℝ) := by
    apply ae_all_iff.mpr
    intro i
    simpa only [dyadicScale, mem_ofPred_eq] using (hprob i).ae_eventually_dyadic
  have hsection := Measure.ae_ae_of_ae_compProd hall
  filter_upwards [hsection, hμ,
    ae_weightedRestrictionKernel_eq P μ (h.aemeasurable_lqgMeasure hμ)
      (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const] with ω hh hloc he
  let : IsLocallyFiniteMeasure (μ ω) := hloc.isLocallyFiniteMeasure
  have hfin : μ ω (ball 0 1) ≠ ∞ := measure_ball_ne_top
  rw [he, normalizedRestriction, withDensity_const, one_smul] at hh
  exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr hfin)).mp hh

/-- The common prescribed-grid count in the physical-radius window of criterion three. -/
theorem exists_ae_singular_mass_common_goodAnnulus_prescribedGrid_physical
    (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧
      ∃ C : ℕ → ℝ, (∀ i, 1 ≤ C i) ∧
      ∀ᵐ ω ∂P, ∀ᵐ w ∂(μ ω).restrict (ball 0 1),
        ∀ i, ∀ᶠ n : ℕ in atTop,
          ∃ z ∈ prevalenceGrid (dyadicScale n),
            dist w z < δ * (s i * (C i * dyadicScale n)) ∧
            (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-(1 / 2 : ℝ))) ≤
              ({r : ℝ | r ∈ Icc (dyadicScale n * s i) (Real.sqrt (dyadicScale n) * s i) ∧
                (∃ k : ℕ, 1 ≤ k ∧ r = s i * (7 : ℝ)⁻¹ ^ k) ∧
                IsGoodAnnulus (μ ω) r z
                  (a / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) (b/2) ∧
                IsGoodAnnulus (μ ω) r w
                  ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b}.ncard : ℝ) := by
  obtain ⟨a, ha, δ, hδ, C, hC, ht⟩ :=
    exists_ae_singular_mass_common_goodAnnulus_prescribedGrid_dyadic
      hball h hμ hμ₀ hAff hCC hγ hγ2 hα hb β hβ s hs
  refine ⟨a, ha, δ, hδ, C, hC, ?_⟩
  filter_upwards [ht] with ω hω
  filter_upwards [hω] with w hw
  intro i
  filter_upwards [hw i, eventually_ge_atTop 9] with n hn hn9
  obtain ⟨z, hz, hdist, hcount⟩ := hn
  exact ⟨z, hz, hdist, scaled_common_criterionThree_count_of_sqrt (hs i) hn9 hcount⟩

end HarmonicBalls.Section6
