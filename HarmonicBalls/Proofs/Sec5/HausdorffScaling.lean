import HarmonicBalls.Defs.HarmonicBall

/-! # Hausdorff continuity under spatial and time changes -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology TopologicalSpace
open scoped Uniformity Pointwise

/-- Uniformly continuous spatial maps induce continuous maps on closed sets
with the Hausdorff uniformity, after taking the closure of the image. -/
theorem continuous_closeds_closure_image {f : ℂ → ℂ} (hf : UniformContinuous f) :
    Continuous (fun A : Closeds ℂ => Closeds.closure (f '' (A : Set ℂ))) := by
  let : UniformSpace (Set ℂ) := UniformSpace.hausdorff ℂ
  exact (Closeds.uniformContinuous_closure.comp
    (hf.image_hausdorff.comp Closeds.uniformContinuous_coe)).continuous

/-- Hausdorff-continuous set families remain continuous after a uniformly
continuous spatial map and a continuous change of time. -/
theorem HausdorffContinuousOn.image_comp {Λ : ℝ → Set ℂ} {T S : Set ℝ}
    (hΛ : HausdorffContinuousOn Λ T) {f : ℂ → ℂ} (hf : UniformContinuous f)
    {g : ℝ → ℝ} (hg : ContinuousOn g S) (hmap : MapsTo g S T) :
    HausdorffContinuousOn (fun t => f '' Λ (g t)) S := by
  rw [hausdorffContinuousOn_iff_continuousOn_closure] at hΛ ⊢
  have hh := (continuous_closeds_closure_image hf).continuousOn.comp
    (hΛ.comp hg hmap) (mapsTo_univ _ _)
  have heq : (fun t => Closeds.closure (f '' Λ (g t))) =
      (fun t => Closeds.closure (f '' closure (Λ (g t)))) := by
    funext t
    apply Closeds.ext
    exact (closure_image_closure hf.continuous).symm
  rw [heq]
  exact hh

/-- Spatial dilations and continuous changes of time preserve Hausdorff
continuity of a family of planar sets. -/
theorem HausdorffContinuousOn.real_smul_comp {Λ : ℝ → Set ℂ} {T S : Set ℝ}
    (hΛ : HausdorffContinuousOn Λ T) (k : ℝ) {g : ℝ → ℝ}
    (hg : ContinuousOn g S) (hmap : MapsTo g S T) :
    HausdorffContinuousOn (fun t => k • Λ (g t)) S := by
  simpa only [Set.image_smul] using hΛ.image_comp (uniformContinuous_const_smul k) hg hmap

end HarmonicBalls
