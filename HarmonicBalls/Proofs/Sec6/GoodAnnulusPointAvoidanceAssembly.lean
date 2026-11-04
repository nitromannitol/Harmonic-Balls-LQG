import HarmonicBalls.Proofs.Sec6.GoodAnnulusRegularLaw
import HarmonicBalls.Proofs.Sec6.GoodAnnulusReduction

/-! # Good-annulus probability from point avoidance

The Section 8 measurable representative and the affine law transfer reduce
Lemma 6.4 to a unit-annulus threshold and planar Brownian point avoidance,
without assuming Borel measurability of the good event itself.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess
open scoped ENNReal NNReal

universe u

/-- Uniform zero-singularity probabilities follow from point avoidance and
positive unit-annulus thresholds on each field realization. -/
theorem goodAnnulus_zero_probability_of_ae_unit_of_point_avoidance
    (hfull : LQGMeasureFullSupportStmt.{u})
    (hatom : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ 0 hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hpolar : ∀ u ∈ sphere (0 : ℂ) (4 * 1),
      ∀ x ∈ annulus 0 (3 * 1) (5 * 1), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
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
    obtain ⟨a, ha, hall⟩ :=
      exists_universal_goodAnnulus_probability_of_ae_unit_of_point_avoidance
        hfull hγ hγ2 (fun Ω _ P hC hcirc => hatom Ω P γ hC hcirc)
        h₀ hμ₀ b hpolar (hunit γ hγ hγ2 Ω₀ P₀ hC₀ hcirc₀ μ₀ h₀ hμ₀ b hb) hp
    refine ⟨a, ha, ?_⟩
    intro Ω _ P hC hcirc μ h hμ r hr z _
    exact hall Ω P hC hcirc μ h hμ (hAff Ω P hC hcirc) (hCC Ω P γ hC hcirc) r hr z
  · refine ⟨1 / 2, by norm_num, ?_⟩
    intro Ω m P hC hcirc μ h hμ r hr z hd
    exact False.elim (hex ⟨Ω, m, P, hC, hcirc, μ, h, hμ⟩)

/-- The frozen good-annulus probability statement follows from Brownian point
avoidance, the unit-annulus threshold and the stated LQG inputs. -/
theorem goodAnnulusProbabilityStmt_of_ae_unit_of_point_avoidance
    (hfull : LQGMeasureFullSupportStmt.{u})
    (hatom : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ 0 hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hpolar : ∀ u ∈ sphere (0 : ℂ) (4 * 1),
      ∀ x ∈ annulus 0 (3 * 1) (5 * 1), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
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
      LQGMeasureWeylScaling P γ 0 hC hcirc) : GoodAnnulusProbabilityStmt.{u} :=
  goodAnnulusProbabilityStmt_of_zero
    (goodAnnulus_zero_probability_of_ae_unit_of_point_avoidance hfull hatom hAff hCC hpolar hunit)
    hex hW

/-- The frozen probability statement follows from the potential hitting and
ball-submean estimates, point avoidance, and the explicit LQG inputs. -/
theorem goodAnnulusProbabilityStmt_of_hitting_bounds_and_point_avoidance
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hatom : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ 0 hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hpolar : ∀ u ∈ sphere (0 : ℂ) (4 * 1),
      ∀ x ∈ annulus 0 (3 * 1) (5 * 1), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    (hbound : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type u) [MeasurableSpace Ω]
      (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc →
      IsLQGMeasureOfField P γ 0 hcirc μ →
      ∀ᵐ ω ∂P, ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
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
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureWeylScaling P γ 0 hC hcirc) : GoodAnnulusProbabilityStmt.{u} := by
  apply goodAnnulusProbabilityStmt_of_ae_unit_of_point_avoidance
    hfull hatom hAff hCC hpolar ?_ hex hW
  intro γ hγ hγ2 Ω _ P hC hcirc μ h hμ b hb
  exact ae_unit_goodAnnulus_threshold_of_hitting_bounds_zeroOne hholder hfull hgrowth
    hγ hγ2 h hμ (hatom Ω P γ hC hcirc) (hAff Ω P hC hcirc)
    (hCC Ω P γ hC hcirc) (hbound γ hγ hγ2 Ω P hC hcirc μ h hμ)
    hC0 hCtop hsubmean hb.1

end HarmonicBalls.Section6
