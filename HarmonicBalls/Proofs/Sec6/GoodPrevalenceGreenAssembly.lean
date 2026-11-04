import HarmonicBalls.Proofs.Sec6.GoodPointAvoidanceScaling
import HarmonicBalls.Proofs.Sec6.GoodAnnulusGreenAssembly

/-! # Good-annulus prevalence from the stopped Green-potential estimate

The prevalence reduction uses Leonardo Bonanno's proof of the Gwynne–Miller
lemma in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess InnerProductSpace
open scoped ENNReal NNReal ContDiff ZeroAtInfty

universe u

/-- Translation reduces planar Brownian point avoidance to paths started at zero. -/
theorem planarBrownianMotion_point_avoidance_of_zero
    (hzero : ∀ x : ℂ, x ≠ 0 →
      ∀ᵐ p ∂(planarBrownianMotion 0), ∀ t : ℝ≥0, p t ≠ x)
    (u x : ℂ) (hxu : x ≠ u) :
    ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x := by
  let T := (Homeomorph.refl ℝ≥0).arrowCongr (Homeomorph.addRight (-u))
  have hmap : (planarBrownianMotion u).map T = planarBrownianMotion 0 := by
    simpa [T] using planarBrownianMotion_map_add_from u (-u)
  have havoid : ∀ᵐ p ∂(planarBrownianMotion u).map T, ∀ t : ℝ≥0, p t ≠ x - u := by
    rw [hmap]
    exact hzero (x - u) (sub_ne_zero.mpr hxu)
  have hpre := ae_of_ae_map T.measurable.aemeasurable havoid
  filter_upwards [hpre] with p hp t hpx
  have hh := hp t
  apply hh
  simp [T, Homeomorph.arrowCongr, hpx, sub_eq_add_neg]

/-- Brownian scaling reduces point avoidance from zero to targets on the unit circle. -/
theorem planarBrownianMotion_point_avoidance_zero_of_unit_circle
    (hunit : ∀ x : ℂ, ‖x‖ = 1 →
      ∀ᵐ p ∂(planarBrownianMotion 0), ∀ t : ℝ≥0, p t ≠ x)
    (x : ℂ) (hx : x ≠ 0) :
    ∀ᵐ p ∂(planarBrownianMotion 0), ∀ t : ℝ≥0, p t ≠ x := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let k : ℝ := ‖x‖⁻¹
  have hk : 0 < k := inv_pos.mpr hr
  let c : ℝ≥0 := ⟨‖x‖ ^ 2, sq_nonneg _⟩
  have hc : 0 < c := by
    change (0 : ℝ) < ‖x‖ ^ 2
    positivity
  have hscale : (Real.sqrt c)⁻¹ = k := by
    change (Real.sqrt (‖x‖ ^ 2))⁻¹ = ‖x‖⁻¹
    rw [Real.sqrt_sq hr.le]
  let T := spacetimePathHomeomorph (Homeomorph.smulOfNeZero k hk.ne') c hc
  have hmap : (planarBrownianMotion 0).map T = planarBrownianMotion 0 := by
    simpa [T] using planarBrownianMotion_map_spacetime_smul 0 hk hc hscale
  have hnorm : ‖k • x‖ = 1 := by
    simp [k, hr.ne']
  have havoid : ∀ᵐ p ∂(planarBrownianMotion 0).map T, ∀ t : ℝ≥0, p t ≠ k • x := by
    rw [hmap]
    exact hunit (k • x) hnorm
  have hpre := ae_of_ae_map T.measurable.aemeasurable havoid
  filter_upwards [hpre] with p hp t hpx
  have hh := hp (c⁻¹ * t)
  apply hh
  simp only [T, spacetimePathHomeomorph_apply, Homeomorph.smulOfNeZero_apply,
    ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul, hpx]

/-- Annular Green symmetry and the generator identification supply the hitting
estimate used in the good-annulus prevalence reduction. -/
theorem goodAnnuliSubRangeStep_of_green_symmetry_and_generator
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
    (hsymm : ∀ x ∈ fineSupportAnnulus 0 1, ∀ y ∈ fineSupportAnnulus 0 1, x ≠ y →
      greenFunction (fineSupportAnnulus 0 1) x y = greenFunction (fineSupportAnnulus 0 1) y x)
    (hgen : ∀ g : ℂ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
        (∀ z, (f : C₀(ℂ, ℝ)) z = g z) ∧
        ∀ z, HarmonicAt g z →
          (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) z = 0)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hsubmean : ∀ K : Set ℂ, IsCompact K → ∀ u ∈ sphere (0 : ℂ) (4 * 1),
      planarBrownianMotion u
        {path | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) path ≤
          ContinuousPath.exitTime Kᶜ path} ≤
      C * ∫⁻ x in ball u (1 / 4 : ℝ), planarBrownianMotion x
        {path | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) path ≤
          ContinuousPath.exitTime Kᶜ path} ∂volume)
    : GoodAnnuliSubRangeStep.{u} := by
  apply goodAnnuliSubRangeStep_of_hitting_bounds_and_unit_point_avoidance
    hholder hfull hgrowth hatom hAff hCC hpolar ?_ hC0 hCtop hsubmean
  intro γ hγ hγ2 Ω _ P hC hcirc μ h hμ
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  filter_upwards [ae_lqg_fineSupport_hitting_bound_of_symmetry
    hholder hfull hgrowth hγ hγ2 hQ h hμ (hatom Ω P γ hC hcirc)
    (fun c r hr x y => fineSupport_green_symmetry_of_unit
      (greenFunction_symmetry_of_interior hsymm) c hr x y) hgen] with sample hsample
  exact Filter.Eventually.of_forall (hsample ·)

/-- It suffices to prove point avoidance for a Brownian motion started at zero
and targets on the unit circle in the Green-potential prevalence reduction. -/
theorem goodAnnuliSubRangeStep_of_green_and_unit_circle_point_avoidance
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
    (hunit : ∀ x : ℂ, ‖x‖ = 1 →
      ∀ᵐ p ∂(planarBrownianMotion 0), ∀ t : ℝ≥0, p t ≠ x)
    (hsymm : ∀ x ∈ fineSupportAnnulus 0 1, ∀ y ∈ fineSupportAnnulus 0 1, x ≠ y →
      greenFunction (fineSupportAnnulus 0 1) x y = greenFunction (fineSupportAnnulus 0 1) y x)
    (hgen : ∀ g : ℂ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
        (∀ z, (f : C₀(ℂ, ℝ)) z = g z) ∧
        ∀ z, HarmonicAt g z →
          (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) z = 0)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hsubmean : ∀ K : Set ℂ, IsCompact K → ∀ u ∈ sphere (0 : ℂ) (4 * 1),
      planarBrownianMotion u
        {path | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) path ≤
          ContinuousPath.exitTime Kᶜ path} ≤
      C * ∫⁻ x in ball u (1 / 4 : ℝ), planarBrownianMotion x
        {path | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) path ≤
          ContinuousPath.exitTime Kᶜ path} ∂volume)
    : GoodAnnuliSubRangeStep.{u} := by
  apply goodAnnuliSubRangeStep_of_green_symmetry_and_generator
    hholder hfull hgrowth hatom hAff hCC ?_ hsymm hgen hC0 hCtop hsubmean
  intro u _ x _ hxu
  exact planarBrownianMotion_point_avoidance_of_zero
    (planarBrownianMotion_point_avoidance_zero_of_unit_circle hunit) u x hxu

end HarmonicBalls.Section6
