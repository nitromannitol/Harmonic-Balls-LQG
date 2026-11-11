import HarmonicBalls.Draft.Section11
import HarmonicBalls.Defs.Annuli
import HarmonicBalls.FirstPass.S11c.GreenTranslate11_7
import HarmonicBalls.Proofs.Sec5.GreenScaling

/-!
# Affine transfer of the pinch event (write-up l.223-225, deterministic part)

For `r > 0` and `z ∈ ℂ` the chart `ψ x = (x - z)/r` (inverse `φ u = r u + z`) carries the pinch event at `(z, r)` of
`(μ, D)` to the pinch event at `(0, 1)` of the pushed-forward measure `μ.map ψ` and of the pulled-back metric
`D (r x + z) (r y + z)`:
`pinchPointEvent μ D U T Q' Q M r z ↔ pinchPointEvent (μ.map ψ) (D ∘ φ) U T Q' Q M 1 0`.

Only deterministic facts are used: image and preimage bookkeeping (`rescaledSet`, `annulus`, sphere), the homeomorphism
property of the chart (`Homeomorph.image_frontier`), and the translation and dilation covariance of the Green function
(`HarmonicBalls.S11c.greenFunction_ball_add`, `greenFunction_ball_smul`). The almost sure identification of
`(μ.map ψ, D ∘ φ)` with the LQG measure and metric of the pulled-back field is the Proposed input
`LQGMeasureCoordChange` / item IV of `LQGMetricFieldAxioms` (Proposed/LQG.lean), not used here.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- The affine chart `x ↦ (x - z)/r` as a measurable equivalence of `ℂ`; its inverse is `u ↦ r u + z`. -/
noncomputable def pinchChart (z : ℂ) {r : ℝ} (hr : r ≠ 0) : ℂ ≃ᵐ ℂ where
  toFun x := (x - z) / (r : ℂ)
  invFun u := (r : ℂ) * u + z
  left_inv x := by
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    show (r : ℂ) * ((x - z) / (r : ℂ)) + z = x
    field_simp
    try ring
  right_inv u := by
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    show ((r : ℂ) * u + z - z) / (r : ℂ) = u
    rw [add_sub_cancel_right, mul_div_cancel_left₀ u hr']
  measurable_toFun := (measurable_id.sub_const z).div_const _
  measurable_invFun := (measurable_id.const_mul _).add_const z

theorem pinchChart_apply {z : ℂ} {r : ℝ} (hr : r ≠ 0) (x : ℂ) :
    pinchChart z hr x = (x - z) / (r : ℂ) := rfl

/-- The rescaled set `rescaledSet A r z = φ '' A` is the preimage under the chart. -/
theorem rescaledSet_eq_preimage (A : Set ℂ) {r : ℝ} (hr : r ≠ 0) (z : ℂ) :
    rescaledSet A r z = (pinchChart z hr) ⁻¹' A := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    show ((r : ℂ) * a + z - z) / (r : ℂ) ∈ A
    rw [add_sub_cancel_right, mul_div_cancel_left₀ a hr']
    exact ha
  · intro hx
    refine ⟨(x - z) / (r : ℂ), hx, ?_⟩
    show (r : ℂ) * ((x - z) / (r : ℂ)) + z = x
    field_simp
    try ring

theorem rescaledSet_one_zero (A : Set ℂ) : rescaledSet A 1 0 = A := by
  simp [rescaledSet]

/-- The sphere of radius `c r` about `z` is the preimage of the sphere of radius `c` about `0`. -/
theorem preimage_sphere_chart {z : ℂ} {r : ℝ} (hr : 0 < r) (c : ℝ) :
    (pinchChart z hr.ne') ⁻¹' sphere (0 : ℂ) c = sphere z (c * r) := by
  ext x
  rw [mem_preimage, mem_sphere_zero_iff_norm, mem_sphere_iff_norm, pinchChart_apply, norm_div,
    Complex.norm_real, Real.norm_of_nonneg hr.le, div_eq_iff hr.ne', mul_comm c r]

/-- The annulus about `0` pulls back to the annulus about `z` (radii scaled by `r`). -/
theorem preimage_annulus_chart {z : ℂ} {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    (pinchChart z hr.ne') ⁻¹' annulus (0 : ℂ) a b = annulus z (a * r) (b * r) := by
  ext x
  simp only [mem_preimage, annulus, Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall,
    dist_eq_norm, sub_zero, pinchChart_apply, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le,
    div_lt_iff₀ hr, div_le_iff₀ hr]

/-- Translation and dilation covariance of the Green function: `G_{B(z, b r)}(r u + z, r v + z) = G_{B(0,b)}(u, v)`. -/
theorem greenFunction_chart (z : ℂ) {r : ℝ} (hr : 0 < r) (b : ℝ) (u v : ℂ) :
    greenFunction (ball z (b * r)) ((r : ℂ) * u + z) ((r : ℂ) * v + z) = greenFunction (ball 0 b) u v := by
  have h1 := HarmonicBalls.S11c.greenFunction_ball_add z (r * b) ((r : ℂ) * u) ((r : ℂ) * v)
  have h2 := greenFunction_ball_smul (R := b) (k := r) hr u v
  rw [Complex.real_smul, Complex.real_smul] at h2
  rw [mul_comm b r, ← h1]
  rw [← h2]

/-- Image of a function under the image of a set (set-level bookkeeping for `setDist`). -/
theorem setDist_rescaledSet (D : ℂ → ℂ → ℝ) (A B : Set ℂ) (r : ℝ) (z : ℂ) :
    setDist D (rescaledSet A r z) (rescaledSet B r z) =
      setDist (fun x y => D ((r : ℂ) * x + z) ((r : ℂ) * y + z)) A B := by
  unfold setDist rescaledSet
  rw [Set.image2_image_left, Set.image2_image_right]

/-- The chart is a homeomorphism, so it commutes with frontiers. -/
theorem frontier_rescaledSet (A : Set ℂ) {r : ℝ} (hr : r ≠ 0) (z : ℂ) :
    frontier (rescaledSet A r z) = rescaledSet (frontier A) r z := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  let h : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ (r : ℂ) hr').trans (Homeomorph.addRight z)
  have hh : ∀ S : Set ℂ, rescaledSet S r z = h '' S := fun S => rfl
  rw [hh, hh, h.image_frontier]

/-- The Green potential of the annulus transforms under the chart (Step 11 / `annulusGreenPotentialSup`). -/
theorem annulusGreenPotentialSup_chart (μ : Measure ℂ) (z : ℂ) {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    annulusGreenPotentialSup μ z (a * r) (b * r) =
      annulusGreenPotentialSup (μ.map (pinchChart z hr.ne')) 0 a b := by
  unfold annulusGreenPotentialSup
  set ψ := pinchChart z hr.ne' with hψ
  have hA : ψ ⁻¹' annulus (0 : ℂ) a b = annulus z (a * r) (b * r) := preimage_annulus_chart hr a b
  have hS : MeasurableSet (annulus (0 : ℂ) a b) := HarmonicBalls.S11c.measurableSet_annulus_centre 0 a b
  have hψm : Measurable ψ := ψ.measurable
  -- inner integrals: transport the integral over `annulus 0 a b` for `μ.map ψ` to the integral over the chart preimage
  have hint : ∀ x : ℂ, ∫⁻ w in annulus (0 : ℂ) a b,
      (if w = ψ x then ∞ else ENNReal.ofReal (greenFunction (ball 0 b) (ψ x) w)) ∂(μ.map ψ) =
      ∫⁻ y in ψ ⁻¹' annulus (0 : ℂ) a b,
      (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball z (b * r)) x y)) ∂μ := by
    intro x
    rw [Measure.restrict_map hψm hS, lintegral_map_equiv]
    refine setLIntegral_congr_fun (hψm hS) (fun y _ => ?_)
    have hyx : ψ y = ψ x ↔ y = x := ψ.injective.eq_iff
    have hx : (r : ℂ) * ψ x + z = x := ψ.left_inv x
    have hy : (r : ℂ) * ψ y + z = y := ψ.left_inv y
    have hG := greenFunction_chart z hr b (ψ x) (ψ y)
    rw [hx, hy] at hG
    by_cases hxy : y = x
    · subst hxy
      simp
    · have hne : ψ y ≠ ψ x := fun h => hxy (hyx.mp h)
      simp only [hne, hxy, ite_false]
      rw [hG]
  rw [← hA]
  let Φ : ℂ → ℝ≥0∞ := fun u => ∫⁻ w in annulus (0 : ℂ) a b,
    (if w = u then ∞ else ENNReal.ofReal (greenFunction (ball 0 b) u w)) ∂(μ.map ψ)
  have h1 : ∀ x : ℂ, ∫⁻ y in ψ ⁻¹' annulus (0 : ℂ) a b,
      (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball z (b * r)) x y)) ∂μ = Φ (ψ x) :=
    fun x => (hint x).symm
  simp only [h1]
  have himg : ψ '' (ψ ⁻¹' annulus (0 : ℂ) a b) = annulus (0 : ℂ) a b :=
    Set.image_preimage_eq _ ψ.surjective
  have key := (iSup_image (f := ψ) (g := Φ) (t := ψ ⁻¹' annulus (0 : ℂ) a b))
  rw [himg] at key
  exact key.symm

/-- Pinch transfer (deterministic). The pinch event at `(z, r)` of `(μ, D)` is the pinch event at `(0, 1)` of the
pushed-forward measure `μ.map ψ` and the pulled-back metric `D (r x + z) (r y + z)`, `ψ x = (x - z)/r`. -/
theorem pinchPointEvent_chart_iff (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M r : ℝ) (z : ℂ)
    (hr : 0 < r) :
    pinchPointEvent μ D U T Q' Q M r z ↔
      pinchPointEvent (μ.map (pinchChart z hr.ne')) (fun x y => D ((r : ℂ) * x + z) ((r : ℂ) * y + z))
        U T Q' Q M 1 0 := by
  have hr' : r ≠ 0 := hr.ne'
  have hsph : sphere z (5 * r) = rescaledSet (sphere 0 5) r z := by
    rw [rescaledSet_eq_preimage _ hr', preimage_sphere_chart hr]
  have hsing : ({z} : Set ℂ) = rescaledSet {0} r z := by
    simp [rescaledSet]
  have hmap : ∀ S : Set ℂ, (μ.map (pinchChart z hr.ne')) S = μ (rescaledSet S r z) := by
    intro S
    rw [rescaledSet_eq_preimage _ hr', MeasurableEquiv.map_apply]
  unfold pinchPointEvent
  rw [hsph, hsing, ← hmap, annulusGreenPotentialSup_chart μ z hr 3 6, frontier_rescaledSet Q hr']
  simp only [setDist_rescaledSet]
  simp only [rescaledSet, iSup_image, mul_zero, zero_add, mul_one, Complex.ofReal_one, one_mul, add_zero,
    Set.image_id']

end HarmonicBalls
