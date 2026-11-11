import HarmonicBalls.Proofs.Sec6.BrownianGermBlocks
import HarmonicBalls.Proofs.Sec6.GoodAnnulusUniversalLaw

/-! # Fine support and the Brownian zero-one law

The Brownian germ zero-one theorem discharges the zero-one premise in the
fine-support and good-annulus reductions. The potential hitting and submean
estimates and the LQG inputs remain explicit.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess Metric
open scoped ENNReal Topology

universe u

/-- The potential hitting estimate implies LQG fine support at almost every
centre, using the Brownian germ zero-one theorem. -/
theorem ae_ae_lqg_fine_support_of_hitting_bounds_zeroOne
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {γ : ℝ}
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
          ContinuousPath.exitTime (ball x (fineSupportScale n)) ω'}) :
    ∀ᵐ ω ∂P, ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
      ∀ E : Set ℂ, MeasurableSet E → (μ ω) (ball x ε \ E) = 0 →
      ∀ᵐ ω' ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω' = 0 :=
  ae_ae_lqg_fine_support_of_hitting_bounds hholder hfull hgrowth hγ hγ2 h hμ
    hnonatom hAff hCC hbound planarBrownian_compact_union_zeroOne

/-- A positive unit-annulus threshold follows from the potential hitting and
submean estimates, with no separate Brownian zero-one assumption. -/
theorem ae_unit_goodAnnulus_threshold_of_hitting_bounds_zeroOne
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
    {b : ℝ} (hb : 0 < b) :
    ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (μ ω) 1 0 a b :=
  ae_unit_goodAnnulus_threshold_of_hitting_bounds hholder hfull hgrowth hγ hγ2 h hμ
    hnonatom hAff hCC hbound planarBrownian_compact_union_zeroOne hC0 hCtop hsubmean hb

/-- Hitting and submean estimates for a reference realization give a threshold
uniform over all field realizations, centres and radii. -/
theorem exists_universal_goodAnnulus_probability_of_hitting_bounds
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
    {b : ℝ} (hb : 0 < b) (hmeas : ∀ n : ℕ, MeasurableSet
      {ν : Measure ℂ | IsGoodAnnulus ν 1 0 ((1 / 2 : ℝ) ^ (n + 1)) b})
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ∞)
    (hsubmean : ∀ K : Set ℂ, IsCompact K → ∀ u ∈ sphere (0 : ℂ) (4 * 1),
      planarBrownianMotion u
        {ω | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ≤
      C * ∫⁻ x in ball u (1 / 4 : ℝ), planarBrownianMotion x
        {ω | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ∂volume)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω')
      (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ' : Ω' → Measure ℂ),
      IsWholePlaneGFF P' hC' hcirc' → IsLQGMeasureOfField P' γ 0 hcirc' μ' →
      WholePlaneGFFAffineInvariance P' hC' hcirc' →
      LQGMeasureCoordChange P' γ 0 hC' hcirc' →
      ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        P' {ω | ¬ IsGoodAnnulus (μ' ω) r z a b} ≤ ENNReal.ofReal (1 - p) := by
  apply exists_universal_goodAnnulus_probability_of_ae_unit hγ hγ2 h hμ hAff hCC b hmeas ?_ hp
  exact ae_unit_goodAnnulus_threshold_of_hitting_bounds_zeroOne hholder hfull hgrowth
    hγ hγ2 h hμ hnonatom hAff hCC hbound hC0 hCtop hsubmean hb

end HarmonicBalls.Section6
