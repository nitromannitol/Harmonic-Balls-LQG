import HarmonicBalls.Proofs.Sec6.GoodAnnulusPointAvoidanceAssembly
import HarmonicBalls.Proofs.Sec6.RecenteredGoodAnnulusLocality
import HarmonicBalls.Steps.Sec11.AnnulusDilation

/-! # Scaling point avoidance on annuli

The prevalence theorem imported below uses Leonardo Bonanno's proof of the
Gwynne–Miller lemma in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6
universe u

open MeasureTheory Metric Set Filter MarkovProcess
open scoped ENNReal NNReal Topology

/-- Brownian spacetime scaling transfers point avoidance on the unit annulus
to the corresponding annulus at any positive radius. -/
theorem annulus_point_avoidance_of_unit
    (hunit : ∀ u ∈ sphere (0 : ℂ) (4 * 1),
      ∀ x ∈ annulus 0 (3 * 1) (5 * 1), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    {r : ℝ} (hr : 0 < r) (u : ℂ) (hu : u ∈ sphere 0 (4 * r))
    (x : ℂ) (hx : x ∈ annulus 0 (3 * r) (5 * r)) (hxu : x ≠ u) :
    ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x := by
  let k : ℝ := r⁻¹
  have hk : 0 < k := inv_pos.mpr hr
  let c : ℝ≥0 := ⟨r ^ 2, sq_nonneg _⟩
  have hc : 0 < c := by
    change (0 : ℝ) < r ^ 2
    positivity
  have hscale : (Real.sqrt c)⁻¹ = k := by
    change (Real.sqrt (r ^ 2))⁻¹ = r⁻¹
    rw [Real.sqrt_sq hr.le]
  let f : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero k hk.ne'
  let T := spacetimePathHomeomorph f c hc
  have hmap : (planarBrownianMotion u).map T = planarBrownianMotion (k • u) :=
    planarBrownianMotion_map_spacetime_smul u hk hc hscale
  have hu' : k • u ∈ sphere (0 : ℂ) (4 * 1) := by
    have hu0 : ‖u‖ = 4 * r := by simpa [mem_sphere, dist_zero_right] using hu
    simp only [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hk, mul_one, hu0, k]
    field_simp
  have hx' : k • x ∈ annulus (0 : ℂ) (3 * 1) (5 * 1) := by
    have h := (smul_mem_annulus_iff hk (0 : ℂ) x (3 * r) (5 * r)).2 hx
    have h3 : k * (3 * r) = 3 * 1 := by dsimp [k]; field_simp
    have h5 : k * (5 * r) = 5 * 1 := by dsimp [k]; field_simp
    simpa only [smul_zero, h3, h5] using h
  have hxu' : k • x ≠ k • u := by
    intro h
    apply hxu
    have he := congrArg (fun y : ℂ => r • y) h
    simpa [k, smul_smul, hr.ne'] using he
  have havoid : ∀ᵐ p ∂(planarBrownianMotion u).map T, ∀ t : ℝ≥0, p t ≠ k • x := by
    rw [hmap]
    exact hunit (k • u) hu' (k • x) hx' hxu'
  have hpre := ae_of_ae_map T.measurable.aemeasurable havoid
  filter_upwards [hpre] with p hp t hpx
  have hh := hp (c⁻¹ * t)
  apply hh
  simp only [T, spacetimePathHomeomorph_apply, f, Homeomorph.smulOfNeZero_apply,
    ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul, hpx]

/-- Good-annulus prevalence follows from the unit threshold and point
avoidance at the unit radius, with the LQG regularity and affine laws. -/
theorem goodAnnuliSubRangeStep_of_ae_unit_and_unit_point_avoidance
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
    (hpolar : ∀ v ∈ sphere (0 : ℂ) (4 * 1),
      ∀ x ∈ annulus 0 (3 * 1) (5 * 1), x ≠ v →
      ∀ᵐ path ∂(planarBrownianMotion v), ∀ t : ℝ≥0, path t ≠ x)
    (hunit : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type u) [MeasurableSpace Ω]
      (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc →
      IsLQGMeasureOfField P γ 0 hcirc μ → ∀ b ∈ Ioo (0 : ℝ) 1,
      ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (μ ω) 1 0 a b) :
    GoodAnnuliSubRangeStep.{u} := by
  apply goodAnnuliSubRangeStep_of_ae_unit_and_point_avoidance hfull hatom hAff hCC
    ?_ hunit
  intro r hr u hu x hx hxu
  exact annulus_point_avoidance_of_unit hpolar hr u hu x hx hxu

/-- The hitting and ball-submean estimates imply good-annulus prevalence,
assuming unit-radius point avoidance and the stated LQG inputs. -/
theorem goodAnnuliSubRangeStep_of_hitting_bounds_and_unit_point_avoidance
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
    : GoodAnnuliSubRangeStep.{u} := by
  apply goodAnnuliSubRangeStep_of_ae_unit_and_unit_point_avoidance
    hfull hatom hAff hCC hpolar ?_
  intro γ hγ hγ2 Ω _ P hC hcirc μ h hμ b hb
  exact ae_unit_goodAnnulus_threshold_of_hitting_bounds_zeroOne hholder hfull hgrowth
    hγ hγ2 h hμ (hatom Ω P γ hC hcirc) (hAff Ω P hC hcirc)
    (hCC Ω P γ hC hcirc) (hbound γ hγ hγ2 Ω P hC hcirc μ h hμ)
    hC0 hCtop hsubmean hb.1

end HarmonicBalls.Section6
