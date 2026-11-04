import HarmonicBalls.Proofs.Sec6.GoodAnnulusPointAvoidanceAssembly
import HarmonicBalls.Proofs.Sec6.GeneralDomainStopped
import HarmonicBalls.Proofs.Sec6.FineSupportLaw

/-! # Good-annulus probability from the stopped Green-potential estimate

The stopped-potential and point-avoidance reductions compose without a separate
assumption of the LQG fine-support hitting bound. The analytic and LQG inputs
remain explicit.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess InnerProductSpace
open scoped ENNReal NNReal ContDiff ZeroAtInfty

universe u

/-- Symmetry off the diagonal in the domain extends to the whole plane,
because the Green function is zero on the diagonal and outside the domain. -/
theorem greenFunction_symmetry_of_interior {O : Set ℂ}
    (hsymm : ∀ x ∈ O, ∀ y ∈ O, x ≠ y → greenFunction O x y = greenFunction O y x) :
    ∀ x y, greenFunction O x y = greenFunction O y x := by
  intro x y
  by_cases hx : x ∈ O
  · by_cases hy : y ∈ O
    · by_cases hxy : x = y
      · subst y
        rfl
      · exact hsymm x hx y hy hxy
    · rw [greenFunction_of_notMem_right hy, greenFunction_of_notMem_left hy]
  · rw [greenFunction_of_notMem_left hx, greenFunction_of_notMem_right hx]

/-- Symmetry on the unit fine-support annulus implies symmetry on every
translated and positively dilated fine-support annulus. -/
theorem fineSupport_green_symmetry_of_unit
    (hsymm : ∀ x y, greenFunction (fineSupportAnnulus 0 1) x y =
      greenFunction (fineSupportAnnulus 0 1) y x)
    (c : ℂ) {r : ℝ} (hr : 0 < r) (x y : ℂ) :
    greenFunction (fineSupportAnnulus c r) x y = greenFunction (fineSupportAnnulus c r) y x := by
  let O := fineSupportAnnulus 0 1
  have hbounded : Bornology.IsBounded O := (fineSupportAnnulus_geometry 0 (by norm_num)).1.1
  let x' : ℂ := r⁻¹ • (x - c)
  let y' : ℂ := r⁻¹ • (y - c)
  have hx : r • x' + c = x := by simp [x', hr.ne']
  have hy : r • y' + c = y := by simp [y', hr.ne']
  have hset : (fun z : ℂ => z + c) '' ((fun z : ℂ => r • z) '' O) =
      fineSupportAnnulus c r := by
    rw [← Set.image_comp]
    exact fineSupportAnnulus_affine c hr
  have hgreen (a b : ℂ) :
      greenFunction (fineSupportAnnulus c r) (r • a + c) (r • b + c) =
        greenFunction O a b := by
    rw [← hset, greenFunction_translate, greenFunction_dilation O hbounded hr]
  calc
    greenFunction (fineSupportAnnulus c r) x y = greenFunction O x' y' := by
      rw [← hx, ← hy, hgreen]
    _ = greenFunction O y' x' := hsymm x' y'
    _ = greenFunction (fineSupportAnnulus c r) y x := by
      rw [← hx, ← hy, hgreen]

/-- The frozen good-annulus statement follows from the stated LQG inputs,
annular Green symmetry, the planar generator identification, point avoidance,
and the ball submean bound. -/
theorem goodAnnulusProbabilityStmt_of_green_symmetry_and_generator
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
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureWeylScaling P γ 0 hC hcirc) : GoodAnnulusProbabilityStmt.{u} := by
  apply goodAnnulusProbabilityStmt_of_hitting_bounds_and_point_avoidance
    hholder hfull hgrowth hatom hAff hCC hpolar ?_ hC0 hCtop hsubmean hex hW
  intro γ hγ hγ2 Ω _ P hC hcirc μ h hμ
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  filter_upwards [ae_lqg_fineSupport_hitting_bound_of_symmetry
    hholder hfull hgrowth hγ hγ2 hQ h hμ (hatom Ω P γ hC hcirc)
    (fun c r hr x y => fineSupport_green_symmetry_of_unit (greenFunction_symmetry_of_interior hsymm) c hr x y) hgen] with sample hsample
  exact Filter.Eventually.of_forall (hsample ·)

end HarmonicBalls.Section6
