import HarmonicBalls.Proofs.Sec6.SingularRootCommonRadii
import HarmonicBalls.Proofs.Sec6.SingularRootGridSmallTolerance

/-! # Common good radii at singular-mass-typical centres

The underlying annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

/-- For a countable family of physical scales, singular-mass-typical centres
and a nearby fine-grid centre share many good radii eventually along dyadic
windows. The fine-grid mesh coefficient may depend on the physical scale. -/
theorem exists_ae_singular_mass_common_goodAnnulus_fineGrid_dyadic
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
      ∃ c : ℕ → ℝ, (∀ i, 0 < c i) ∧
      ∀ᵐ ω ∂P, ∀ᵐ w ∂(μ ω).restrict (ball 0 1),
        ∀ i, ∀ᶠ n : ℕ in atTop,
          ∃ z ∈ prevalenceGrid (c i * dyadicScale n),
            dist w z < δ * (s i * dyadicScale n) ∧
            (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
              ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
                (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
                IsGoodAnnulus (μ ω) (s i*r) z
                  (a / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) (b/2) ∧
                IsGoodAnnulus (μ ω) (s i*r) w
                  ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b}.ncard : ℝ) := by
  classical
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  obtain ⟨a, ha, δ, hδ, ht⟩ := exists_singular_root_common_goodAnnulus_fineGrid
    hball h hμ hμ₀ hAff hCC hγ hγ2 hα hb β hβ
  have hc : ∀ i, ∃ c : ℝ, 0 < c ∧ PolyHighProb
      (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
      (fun ε => {p | ∃ z ∈ prevalenceGrid (c*ε),
        dist p.2 z < δ * (s i*ε) ∧
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
            IsGoodAnnulus (μ p.1) (s i*r) z
              (a / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) (b/2) ∧
            IsGoodAnnulus (μ p.1) (s i*r) p.2
              ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b}.ncard : ℝ)}) :=
    fun i => ht (s i) (hs i)
  choose c hcpos hprob using hc
  refine ⟨a, ha, δ, hδ, c, hcpos, ?_⟩
  have hall : ∀ᵐ p ∂(P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
      (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const),
      ∀ i, ∀ᶠ n : ℕ in atTop,
        ∃ z ∈ prevalenceGrid (c i * dyadicScale n),
          dist p.2 z < δ * (s i * dyadicScale n) ∧
          (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
            ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
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

/-- Prescribed-grid prevalence holds simultaneously with common good radii
at a singular-mass-typical centre and a nearby, possibly finer grid centre. -/
theorem exists_ae_singular_mass_prescribed_grid_and_common_radii
    (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hE₀ : LQGMeasureExistence P γ 0 hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ c₀ a₀ a δ : ℝ, 0 < c₀ ∧ a₀ ∈ Ioo (0 : ℝ) 1 ∧
      a ∈ Ioo (0 : ℝ) 1 ∧ 0 < δ ∧
      ∃ c : ℕ → ℝ, (∀ i, 0 < c i) ∧
      ∀ᵐ ω ∂P, ∀ᵐ w ∂(μ ω).restrict (ball 0 1),
        (∀ᶠ n : ℕ in atTop, ∀ y ∈ prevalenceGrid (dyadicScale n),
          c₀ * Real.logb 7 ((dyadicScale n) ^ (-(1 / 2 : ℝ))) ≤
            ({r : ℝ | r ∈ Icc (dyadicScale n) (Real.sqrt (dyadicScale n)) ∧
              (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus (μ ω) r y a₀ b}.ncard : ℝ)) ∧
        (∀ i, ∀ᶠ n : ℕ in atTop,
          ∃ z ∈ prevalenceGrid (c i * dyadicScale n),
            dist w z < δ * (s i * dyadicScale n) ∧
            (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
              ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
                (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
                IsGoodAnnulus (μ ω) (s i*r) z
                  (a / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) (b/2) ∧
                IsGoodAnnulus (μ ω) (s i*r) w
                  ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b}.ncard : ℝ)) := by
  have hgrowth := lqgVolumeGrowthAllScalesStmt_of_ballMass hball
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := hE₀ h hγ hγ2 hQ
  obtain ⟨c₀, a₀, hc₀, ha₀, hgrid⟩ :=
    goodAnnuli_prevalence_all_singularities_of_zero_existence
      (goodAnnuliSubRangeStep_of_volumeGrowth_fineSupport hgrowth)
      P γ hγ hγ2 hC hcirc h hE₀ hb (abs_nonneg α)
  obtain ⟨a, ha, δ, hδ, c, hc, hroot⟩ :=
    exists_ae_singular_mass_common_goodAnnulus_fineGrid_dyadic
      hball h hμ hμ₀ hAff hCC hγ hγ2 hα hb.1 β hβ s hs
  refine ⟨c₀, a₀, a, δ, hc₀, ha₀, ha, hδ, c, hc, ?_⟩
  filter_upwards [hgrid.ae_eventually_dyadic, hroot, hμ] with ω hg hr hlim
  filter_upwards [hr] with w hw
  refine ⟨?_, hw⟩
  filter_upwards [hg] with n hn
  exact hn α le_rfl (μ ω) hlim

end HarmonicBalls.Section6
