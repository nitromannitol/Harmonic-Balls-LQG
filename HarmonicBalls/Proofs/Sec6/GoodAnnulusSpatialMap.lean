import HarmonicBalls.Proofs.Sec6.ExitTimeSpatialMap
import HarmonicBalls.Proofs.Sec6.BrownianScaling
import HarmonicBalls.Defs.Annuli
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! # Transport of good annuli

A spacetime path-law identity and the corresponding geometric identities
transport the good-annulus predicate under a spatial homeomorphism.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set MarkovProcess
open scoped ENNReal Pointwise

/-- A spatial homeomorphism transports good annuli when its spacetime path
homeomorphism transports the Brownian laws and maps the annulus and circle. -/
theorem isGoodAnnulus_map_of_spacetime_law
    (f : ℂ ≃ₜ ℂ) (c : NNReal) (hc : 0 < c)
    (hpath : ∀ x, (planarBrownianMotion x).map (spacetimePathHomeomorph f c hc) =
      planarBrownianMotion (f x))
    (μ : Measure ℂ) (r s : ℝ) (z w : ℂ) (a b : ℝ)
    (hA : f '' annulus z (3 * r) (5 * r) = annulus w (3 * s) (5 * s))
    (hS : f '' sphere z (4 * r) = sphere w (4 * s))
    (hg : IsGoodAnnulus μ r z a b) : IsGoodAnnulus (μ.map f) s w a b := by
  intro Y hY hYA hmass u hu
  let X := f ⁻¹' Y
  have hX : MeasurableSet X := f.measurable hY
  have hXA : X ⊆ annulus z (3 * r) (5 * r) := by
    intro x hx
    have : f x ∈ f '' annulus z (3 * r) (5 * r) := hA.symm ▸ hYA hx
    obtain ⟨y, hy, heq⟩ := this
    exact f.injective heq ▸ hy
  have hXY : f '' X = Y := image_preimage_eq Y f.surjective
  have hmass' : μ X ≤ ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) := by
    rw [Measure.map_apply f.measurable hY] at hmass
    rw [← hA, f.measurableEmbedding.map_apply, preimage_image_eq _ f.injective] at hmass
    exact hmass
  obtain ⟨v, hv, huv⟩ := hS.symm ▸ hu
  have hprob := hg X hX hXA hmass' v hv
  have heq := measure_exitTime_order_eq_of_spacetime_homeomorph f
    (annulus z (3 * r) (5 * r)) X c hc (planarBrownianMotion v)
    (planarBrownianMotion (f v)) (hpath v)
  rw [hA, hXY, huv] at heq
  rw [heq]
  exact hprob

/-- Under a spacetime path-law identity, the good-annulus condition is
equivalent on an annulus and its image. -/
theorem isGoodAnnulus_map_iff_of_spacetime_law
    (f : ℂ ≃ₜ ℂ) (c : NNReal) (hc : 0 < c)
    (hpath : ∀ x, (planarBrownianMotion x).map (spacetimePathHomeomorph f c hc) =
      planarBrownianMotion (f x))
    (μ : Measure ℂ) (r s : ℝ) (z w : ℂ) (a b : ℝ)
    (hA : f '' annulus z (3 * r) (5 * r) = annulus w (3 * s) (5 * s))
    (hS : f '' sphere z (4 * r) = sphere w (4 * s)) :
    IsGoodAnnulus (μ.map f) s w a b ↔ IsGoodAnnulus μ r z a b := by
  constructor
  · intro hg Y hY hYA hmass u hu
    have hY' : MeasurableSet (f '' Y) := f.measurableEmbedding.measurableSet_image.mpr hY
    have hYA' : f '' Y ⊆ annulus w (3 * s) (5 * s) := by
      rw [← hA]
      exact image_mono hYA
    have hmass' : (μ.map f) (f '' Y) ≤
        ENNReal.ofReal a * (μ.map f) (annulus w (3 * s) (5 * s)) := by
      rw [← hA, f.measurableEmbedding.map_apply, f.measurableEmbedding.map_apply,
        preimage_image_eq _ f.injective, preimage_image_eq _ f.injective]
      exact hmass
    have hu' : f u ∈ sphere w (4 * s) := hS ▸ mem_image_of_mem f hu
    have hprob := hg (f '' Y) hY' hYA' hmass' (f u) hu'
    have heq := measure_exitTime_order_eq_of_spacetime_homeomorph f
      (annulus z (3 * r) (5 * r)) Y c hc (planarBrownianMotion u)
      (planarBrownianMotion (f u)) (hpath u)
    rw [hA] at heq
    rwa [heq] at hprob
  · exact isGoodAnnulus_map_of_spacetime_law f c hc hpath μ r s z w a b hA hS

/-- Positive spatial dilation preserves the good-annulus condition when the
associated Brownian spacetime law is transported. -/
theorem isGoodAnnulus_map_smul_iff_of_spacetime_law
    {k : ℝ} (hk : 0 < k) (c : NNReal) (hc : 0 < c)
    (hpath : ∀ x, (planarBrownianMotion x).map
        (spacetimePathHomeomorph (Homeomorph.smulOfNeZero k hk.ne') c hc) =
      planarBrownianMotion (k • x))
    (μ : Measure ℂ) (r : ℝ) (z : ℂ) (a b : ℝ) :
    IsGoodAnnulus (μ.map (fun x : ℂ => k • x)) (k * r) (k • z) a b ↔
      IsGoodAnnulus μ r z a b := by
  let f : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero k hk.ne'
  have hA : f '' annulus z (3 * r) (5 * r) =
      annulus (k • z) (3 * (k * r)) (5 * (k * r)) := by
    rw [annulus, image_sdiff f.injective]
    change k • ball z (5 * r) \ k • closedBall z (3 * r) = _
    rw [_root_.smul_ball hk.ne', _root_.smul_closedBall' hk.ne',
      Real.norm_eq_abs, abs_of_pos hk]
    congr 2 <;> ring
  have hS : f '' sphere z (4 * r) = sphere (k • z) (4 * (k * r)) := by
    change k • sphere z (4 * r) = _
    rw [_root_.smul_sphere' hk.ne', Real.norm_eq_abs, abs_of_pos hk]
    congr 1
    ring
  exact isGoodAnnulus_map_iff_of_spacetime_law f c hc hpath μ r (k * r) z (k • z) a b hA hS

/-- The inverse-dilation form used for good-radius counts. -/
theorem isGoodAnnulus_map_inv_smul_iff_of_spacetime_law
    {k : ℝ} (hk : 0 < k) (c : NNReal) (hc : 0 < c)
    (hpath : ∀ x, (planarBrownianMotion x).map
        (spacetimePathHomeomorph (Homeomorph.smulOfNeZero k⁻¹ (inv_pos.mpr hk).ne') c hc) =
      planarBrownianMotion (k⁻¹ • x))
    (μ : Measure ℂ) (r : ℝ) (z : ℂ) (a b : ℝ) :
    IsGoodAnnulus (μ.map (fun x : ℂ => k⁻¹ • x)) r z a b ↔
      IsGoodAnnulus μ (k * r) (k • z) a b := by
  have h := isGoodAnnulus_map_smul_iff_of_spacetime_law (inv_pos.mpr hk) c hc hpath
    μ (k * r) (k • z) a b
  simpa only [← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul, smul_smul, one_smul] using h

/-- Positive dilation preserves the good-annulus condition. -/
theorem isGoodAnnulus_map_smul_iff
    {k : ℝ} (hk : 0 < k) (μ : Measure ℂ) (r : ℝ) (z : ℂ) (a b : ℝ) :
    IsGoodAnnulus (μ.map (fun x : ℂ => k • x)) (k * r) (k • z) a b ↔
      IsGoodAnnulus μ r z a b := by
  let c : NNReal := ⟨(k⁻¹) ^ 2, sq_nonneg _⟩
  have hc : 0 < c := by
    change (0 : ℝ) < (k⁻¹) ^ 2
    positivity
  have hscale : (Real.sqrt c)⁻¹ = k := by
    change (Real.sqrt ((k⁻¹) ^ 2))⁻¹ = k
    rw [Real.sqrt_sq (le_of_lt (inv_pos.mpr hk)), inv_inv]
  apply isGoodAnnulus_map_smul_iff_of_spacetime_law hk c hc
  intro x
  exact planarBrownianMotion_map_spacetime_smul x hk hc hscale

/-- Inverse-dilation transport in the form used for good-radius counts. -/
theorem isGoodAnnulus_map_inv_smul_iff
    {k : ℝ} (hk : 0 < k) (μ : Measure ℂ) (r : ℝ) (z : ℂ) (a b : ℝ) :
    IsGoodAnnulus (μ.map (fun x : ℂ => k⁻¹ • x)) r z a b ↔
      IsGoodAnnulus μ (k * r) (k • z) a b := by
  have h := isGoodAnnulus_map_smul_iff (inv_pos.mpr hk) μ (k * r) (k • z) a b
  simpa only [← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul, smul_smul, one_smul] using h

/-- Translation preserves the good-annulus condition. -/
theorem isGoodAnnulus_map_add_iff
    (y : ℂ) (μ : Measure ℂ) (r : ℝ) (z : ℂ) (a b : ℝ) :
    IsGoodAnnulus (μ.map (fun x : ℂ => x + y)) r (z + y) a b ↔
      IsGoodAnnulus μ r z a b := by
  let f : ℂ ≃ₜ ℂ := Homeomorph.addRight y
  have hpath (x : ℂ) : (planarBrownianMotion x).map (spacetimePathHomeomorph f 1 zero_lt_one) =
      planarBrownianMotion (f x) := by
    change (planarBrownianMotion x).map (spacetimePathHomeomorph f 1 zero_lt_one) =
      planarBrownianMotion (x + y)
    convert planarBrownianMotion_map_add_from x y using 1
    congr 1
    funext ω
    ext t
    simp only [spacetimePathHomeomorph_apply, one_mul]
    rfl
  have hA : f '' annulus z (3 * r) (5 * r) = annulus (z + y) (3 * r) (5 * r) := by
    have hm (w : ℂ) : w + y ∈ annulus (z + y) (3 * r) (5 * r) ↔
        w ∈ annulus z (3 * r) (5 * r) := by
      simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, dist_eq_norm,
        add_sub_add_right_eq_sub]
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hm v).mpr hv
    · intro hw
      refine ⟨w - y, (hm (w - y)).mp ?_, by simp [f]⟩
      simpa only [sub_add_cancel] using hw
  have hS : f '' sphere z (4 * r) = sphere (z + y) (4 * r) := by
    have hm (w : ℂ) : w + y ∈ sphere (z + y) (4 * r) ↔ w ∈ sphere z (4 * r) := by
      simp only [mem_sphere, dist_eq_norm, add_sub_add_right_eq_sub]
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hm v).mpr hv
    · intro hw
      refine ⟨w - y, (hm (w - y)).mp ?_, by simp [f]⟩
      simpa only [sub_add_cancel] using hw
  exact isGoodAnnulus_map_iff_of_spacetime_law f 1 zero_lt_one hpath μ r r z (z + y) a b hA hS

end HarmonicBalls.Section6
