import Mathlib
import MarkovProcess.Examples.HeatSemigroup

/-! # The planar heat semigroup

The transition semigroup of standard planar Brownian motion on `ℂ`: at time `t` from `z` the
transition law is the product of the real Gaussians of means `Re z`, `Im z` and variance `t`,
read on `ℂ` through `Complex.measurableEquivRealProd`. Its generator is `Δ/2`.

This file defines the semigroup as a `MarkovProcess.SubMarkovKernelSemigroup ℂ` (the conjugate of
the parallel product `heatKernel t ∥ₖ heatKernel t` of two one-dimensional heat kernels) and proves
that it is conservative.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal NNReal


/-- The planar Gaussian law with mean `z` and covariance `t · I₂`: the image on `ℂ` of the product
of the real Gaussians `𝒩(Re z, t)` and `𝒩(Im z, t)`. -/
noncomputable def planarGaussian (z : ℂ) (t : ℝ≥0) : Measure ℂ :=
  ((gaussianReal z.re t).prod (gaussianReal z.im t)).map Complex.measurableEquivRealProd.symm

instance isProbabilityMeasure_planarGaussian (z : ℂ) (t : ℝ≥0) :
    IsProbabilityMeasure (planarGaussian z t) :=
  ⟨by rw [planarGaussian, Measure.map_apply Complex.measurableEquivRealProd.symm.measurable
      MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩

/-- The transition kernel of the planar heat semigroup at time `t`: the parallel product of two
one-dimensional heat kernels, conjugated to `ℂ`. -/
noncomputable def planarHeatKernel (t : ℝ≥0) : Kernel ℂ ℂ :=
  ((heatKernel t ∥ₖ heatKernel t).comap Complex.measurableEquivRealProd Complex.measurableEquivRealProd.measurable).map Complex.measurableEquivRealProd.symm

instance isMarkovKernel_planarHeatKernel (t : ℝ≥0) : IsMarkovKernel (planarHeatKernel t) :=
  Kernel.IsMarkovKernel.map _ Complex.measurableEquivRealProd.symm.measurable

theorem planarHeatKernel_apply (t : ℝ≥0) (z : ℂ) : planarHeatKernel t z = planarGaussian z t := by
  rw [planarHeatKernel, Kernel.map_apply _ Complex.measurableEquivRealProd.symm.measurable, Kernel.comap_apply,
    Kernel.parallelComp_apply, heatKernel_apply, heatKernel_apply, planarGaussian]
  rfl

instance isMarkovKernel_heatKernelJoint : IsMarkovKernel heatKernelJoint :=
  ⟨fun p ↦ by rw [heatKernelJoint_apply]; infer_instance⟩

/-- The joint kernel `(t, z) ↦ planarGaussian z t`. -/
noncomputable def planarHeatKernelJoint : Kernel (ℝ≥0 × ℂ) ℂ :=
  ((heatKernelJoint.comap (fun p : ℝ≥0 × ℂ ↦ (p.1, p.2.re)) (by fun_prop)) ×ₖ
    (heatKernelJoint.comap (fun p : ℝ≥0 × ℂ ↦ (p.1, p.2.im)) (by fun_prop))).map Complex.measurableEquivRealProd.symm

theorem planarHeatKernelJoint_apply (p : ℝ≥0 × ℂ) :
    planarHeatKernelJoint p = planarGaussian p.2 p.1 := by
  rw [planarHeatKernelJoint, Kernel.map_apply _ Complex.measurableEquivRealProd.symm.measurable, Kernel.prod_apply,
    Kernel.comap_apply, Kernel.comap_apply, heatKernelJoint_apply, heatKernelJoint_apply,
    planarGaussian]

theorem planarGaussian_zero (z : ℂ) : planarGaussian z 0 = Measure.dirac z := by
  rw [planarGaussian, gaussianReal_zero_var, gaussianReal_zero_var,
    Measure.dirac_prod_dirac]
  ext B hB
  rw [Measure.map_apply Complex.measurableEquivRealProd.symm.measurable hB,
    Measure.dirac_apply' _ (Complex.measurableEquivRealProd.symm.measurable hB),
    Measure.dirac_apply' _ hB]
  rfl

theorem planarHeatKernel_comp (s t : ℝ≥0) :
    planarHeatKernel t ∘ₖ planarHeatKernel s = planarHeatKernel (s + t) := by
  have hA : (heatKernel t ∥ₖ heatKernel t) ∘ₖ (heatKernel s ∥ₖ heatKernel s) =
      heatKernel (s + t) ∥ₖ heatKernel (s + t) := by
    rw [Kernel.parallelComp_comp_parallelComp]
    have h := heatSemigroup.kernel_add s t
    exact congrArg₂ _ h.symm h.symm
  set e := Complex.measurableEquivRealProd
  have h1 : (((heatKernel t ∥ₖ heatKernel t).comap e e.measurable).map e.symm).comap e.symm
      e.symm.measurable = (heatKernel t ∥ₖ heatKernel t).map e.symm := by
    ext w : 1
    rw [Kernel.comap_apply, Kernel.map_apply _ e.symm.measurable, Kernel.comap_apply,
      Kernel.map_apply _ e.symm.measurable, e.apply_symm_apply]
  have h2 : (heatKernel t ∥ₖ heatKernel t) ∘ₖ (heatKernel s ∥ₖ heatKernel s).comap e e.measurable =
      ((heatKernel t ∥ₖ heatKernel t) ∘ₖ (heatKernel s ∥ₖ heatKernel s)).comap e e.measurable := by
    ext z : 1
    rw [Kernel.comp_apply, Kernel.comap_apply, Kernel.comap_apply, Kernel.comp_apply]
  rw [planarHeatKernel, planarHeatKernel, Kernel.comp_map, h1, ← Kernel.map_comp, h2, hA]
  · rfl
  · exact e.symm.measurable

/-- **The planar heat semigroup**, the transition semigroup of standard planar Brownian motion:
its transition law at time `t` from `z` is `planarGaussian z t`. -/
noncomputable def planarHeatSemigroup : SubMarkovKernelSemigroup ℂ where
  kernel := planarHeatKernel
  measurable_kernel := by
    have hfun : (fun p : ℝ≥0 × ℂ ↦ planarHeatKernel p.1 p.2) = fun p ↦ planarHeatKernelJoint p :=
      funext fun p ↦ by rw [planarHeatKernel_apply, planarHeatKernelJoint_apply]
    rw [hfun]
    exact planarHeatKernelJoint.measurable
  kernel_zero := Kernel.ext fun z ↦ by
    rw [planarHeatKernel_apply, planarGaussian_zero, Kernel.id_apply]
  kernel_add := fun s t ↦ (planarHeatKernel_comp s t).symm
  isSubMarkovKernel := fun _ ↦ IsSubMarkovKernel.of_isMarkovKernel _

@[simp]
theorem planarHeatSemigroup_apply (t : ℝ≥0) (z : ℂ) :
    planarHeatSemigroup t z = planarGaussian z t :=
  planarHeatKernel_apply t z

/-- The planar heat semigroup is conservative. -/
theorem isConservative_planarHeatSemigroup : planarHeatSemigroup.IsConservative := by
  intro t z
  rw [planarHeatSemigroup_apply]
  exact measure_univ

/-- The standard planar Gaussian `planarGaussian 0 1`. -/
noncomputable abbrev stdPlanarGaussian : Measure ℂ := planarGaussian 0 1

/-- **Scaling representation**: `planarGaussian z t` is the law of `z + √t · w` for `w` a standard
planar Gaussian. -/
theorem planarGaussian_eq_map_add_sqrt_mul (z : ℂ) (t : ℝ≥0) :
    planarGaussian z t = stdPlanarGaussian.map (fun w ↦ z + (Real.sqrt t : ℂ) * w) := by
  have he := Complex.measurableEquivRealProd.symm.measurable
  rw [stdPlanarGaussian, planarGaussian, planarGaussian, Complex.zero_re, Complex.zero_im,
    gaussianReal_eq_map_add_sqrt_mul z.re, gaussianReal_eq_map_add_sqrt_mul z.im,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), Measure.map_map he (by fun_prop),
    Measure.map_map (by fun_prop) he]
  congr 1
  funext w
  apply Complex.ext <;> simp [Complex.measurableEquivRealProd]

end HarmonicBalls
