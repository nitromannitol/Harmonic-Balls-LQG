import Mathlib
import HarmonicBalls.Defs.Brownian
import HarmonicBalls.Proofs.Brownian.PlanarHeatSemigroup

/-! # Planar Brownian motion is the continuous-path process of the planar heat semigroup

`planarBrownianMotion` (Defs/Brownian.lean) is defined as the law of `𝓑¹ + i 𝓑²` for independent real
Brownian motions. This file identifies it with MarkovProcess's continuous-path process of the planar
heat semigroup `planarHeatSemigroup` (Proofs/Brownian/PlanarHeatSemigroup.lean):

* `hasKolmogorovMoments_planarHeatSemigroup`: `E_z |𝓑_h - z|⁴ ≤ M h²` (Kolmogorov moment criterion);
* `finiteTimeKernel_planarHeatSemigroup`: the finite-dimensional laws of the planar heat semigroup
  are the products of those of the one-dimensional heat semigroup, read on `ℂ`;
* `planarBrownianMotion_eq_continuousProcess`: `planarBrownianMotion` is the continuous-path process
  of `planarHeatSemigroup` (uniqueness theorem of MarkovProcess, Main.lean).
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal NNReal

section Moments

theorem stdPlanarGaussian_map_re : stdPlanarGaussian.map Complex.re = gaussianReal 0 1 := by
  have he := Complex.measurableEquivRealProd.symm.measurable
  rw [stdPlanarGaussian, planarGaussian, Measure.map_map Complex.measurable_re he]
  have hfst : Complex.re ∘ Complex.measurableEquivRealProd.symm = Prod.fst := by
    funext p; simp [Complex.measurableEquivRealProd]
  rw [hfst, Measure.map_fst_prod, measure_univ, one_smul, Complex.zero_re]

theorem stdPlanarGaussian_map_im : stdPlanarGaussian.map Complex.im = gaussianReal 0 1 := by
  have he := Complex.measurableEquivRealProd.symm.measurable
  rw [stdPlanarGaussian, planarGaussian, Measure.map_map Complex.measurable_im he]
  have hsnd : Complex.im ∘ Complex.measurableEquivRealProd.symm = Prod.snd := by
    funext p; simp [Complex.measurableEquivRealProd]
  rw [hsnd, Measure.map_snd_prod, measure_univ, one_smul, Complex.zero_im]

/-- The fourth moment of the standard planar Gaussian is at most `16` times that of the standard
real Gaussian. -/
theorem lintegral_enorm_rpow_stdPlanarGaussian_le :
    ∫⁻ w, ‖w‖ₑ ^ (4 : ℝ) ∂stdPlanarGaussian ≤ ((16 * gaussianFourthMoment : ℝ≥0) : ℝ≥0∞) := by
  have hpt : ∀ w : ℂ, ‖w‖ₑ ^ (4 : ℝ) ≤ 2 ^ ((4 : ℝ) - 1) * (‖w.re‖ₑ ^ (4 : ℝ) + ‖w.im‖ₑ ^ (4 : ℝ)) :=
    fun w ↦ (ENNReal.rpow_le_rpow (by
      rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _)
        (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (Complex.norm_le_abs_re_add_abs_im w)) (by norm_num)).trans
      (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by norm_num))
  have hre : ∫⁻ w, ‖w.re‖ₑ ^ (4 : ℝ) ∂stdPlanarGaussian = gaussianFourthMoment := by
    rw [coe_gaussianFourthMoment, ← stdPlanarGaussian_map_re,
      lintegral_map (by fun_prop) Complex.measurable_re]
    simp only [ENNReal.rpow_ofNat]
  have him : ∫⁻ w, ‖w.im‖ₑ ^ (4 : ℝ) ∂stdPlanarGaussian = gaussianFourthMoment := by
    rw [coe_gaussianFourthMoment, ← stdPlanarGaussian_map_im,
      lintegral_map (by fun_prop) Complex.measurable_im]
    simp only [ENNReal.rpow_ofNat]
  calc ∫⁻ w, ‖w‖ₑ ^ (4 : ℝ) ∂stdPlanarGaussian
      ≤ ∫⁻ w, 2 ^ ((4 : ℝ) - 1) * (‖w.re‖ₑ ^ (4 : ℝ) + ‖w.im‖ₑ ^ (4 : ℝ)) ∂stdPlanarGaussian :=
        lintegral_mono hpt
    _ = 2 ^ ((4 : ℝ) - 1) * (gaussianFourthMoment + gaussianFourthMoment) := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_add_left (by fun_prop), hre, him]
    _ = ((16 * gaussianFourthMoment : ℝ≥0) : ℝ≥0∞) := by
        rw [show (4 : ℝ) - 1 = (3 : ℕ) by norm_num, ENNReal.rpow_natCast]
        push_cast
        ring

/-- **The planar heat semigroup satisfies the Kolmogorov moment criterion** with exponents `p = 4`,
`q = 2`: `E_z |𝓑_h - z|⁴ ≤ 16 m₄ h²`, `m₄` the fourth moment of the standard real Gaussian. -/
theorem hasKolmogorovMoments_planarHeatSemigroup :
    planarHeatSemigroup.HasKolmogorovMoments 4 2 (16 * gaussianFourthMoment) := by
  refine ⟨by norm_num, by norm_num, fun h y ↦ ?_⟩
  rw [planarHeatSemigroup_apply, planarGaussian_eq_map_add_sqrt_mul,
    lintegral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ w : ℂ, edist (y + (Real.sqrt h : ℂ) * w) y ^ (4 : ℝ) =
      (h : ℝ≥0∞) ^ (2 : ℝ) * ‖w‖ₑ ^ (4 : ℝ) := by
    intro w
    rw [edist_eq_enorm_sub, add_sub_cancel_left, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _
      (by norm_num)]
    congr 1
    rw [show (4 : ℝ) = 2 * 2 by norm_num, ENNReal.rpow_mul]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num),
      Real.rpow_two, Real.sq_sqrt h.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  simp_rw [hpt]
  rw [lintegral_const_mul _ (by fun_prop), mul_comm]
  exact mul_le_mul_left lintegral_enorm_rpow_stdPlanarGaussian_le _

/-- The planar heat semigroup is Kolmogorov regular. -/
theorem kolmogorovRegular_planarHeatSemigroup :
    planarHeatSemigroup.KolmogorovRegular isConservative_planarHeatSemigroup :=
  SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
    isConservative_planarHeatSemigroup hasKolmogorovMoments_planarHeatSemigroup

end Moments

section FiniteDimensional

/-- Assemble a `ℂ`-valued coordinate path from its real and imaginary coordinate paths. -/
noncomputable def complexCoordPathOfReIm {ι : Type*} (p : (ι → ℝ) × (ι → ℝ)) : ι → ℂ :=
  fun i ↦ Complex.measurableEquivRealProd.symm (p.1 i, p.2 i)

theorem measurable_complexCoordPathOfReIm {ι : Type*} :
    Measurable (complexCoordPathOfReIm (ι := ι)) :=
  measurable_pi_iff.mpr fun i ↦ Complex.measurableEquivRealProd.symm.measurable.comp
    (((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))

theorem complexCoordPathOfReIm_cons {n : ℕ} (a b : ℝ) (p q : Fin n → ℝ) :
    complexCoordPathOfReIm
        (@Fin.cons n (fun _ ↦ ℝ) a p, @Fin.cons n (fun _ ↦ ℝ) b q) =
      @Fin.cons n (fun _ ↦ ℂ) (Complex.measurableEquivRealProd.symm (a, b))
        (complexCoordPathOfReIm (p, q)) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [complexCoordPathOfReIm]
  · simp [complexCoordPathOfReIm]

/-- Tonelli for the product of two kernel compositions-products, with the two outer integrals
first. -/
theorem lintegral_prod_compProd_apply {X Y Z X' Y' Z' : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace X'] [MeasurableSpace Y']
    [MeasurableSpace Z'] (κ : Kernel X Y) (η : Kernel (X × Y) Z) (κ' : Kernel X' Y')
    (η' : Kernel (X' × Y') Z') [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel κ']
    [IsSFiniteKernel η'] (x : X) (x' : X') {F : (Y × Z) × (Y' × Z') → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ v, F v ∂(((κ ⊗ₖ η) x).prod ((κ' ⊗ₖ η') x')) =
      ∫⁻ a, ∫⁻ c, ∫⁻ b, ∫⁻ d, F ((a, b), (c, d)) ∂η' (x', c) ∂η (x, a) ∂κ' x' ∂κ x := by
  rw [lintegral_prod _ hF.aemeasurable, Kernel.lintegral_compProd _ _ _ hF.lintegral_prod_right']
  refine lintegral_congr fun a ↦ ?_
  have hin : ∀ b, ∫⁻ v', F ((a, b), v') ∂(κ' ⊗ₖ η') x' =
      ∫⁻ c, ∫⁻ d, F ((a, b), (c, d)) ∂η' (x', c) ∂κ' x' := fun b ↦
    Kernel.lintegral_compProd _ _ _ (hF.comp measurable_prodMk_left)
  simp only [hin]
  let ζ : Kernel (Z × Y') Z' := Kernel.prodMkLeft Z (η'.comap (fun c ↦ (x', c)) measurable_prodMk_left)
  have hmeas : Measurable fun bc : Z × Y' ↦ ∫⁻ d, F ((a, bc.1), (bc.2, d)) ∂ζ bc :=
    Measurable.lintegral_kernel_prod_right' (κ := ζ)
      (f := fun x : (Z × Y') × Z' ↦ F ((a, x.1.1), (x.1.2, x.2))) (hF.comp (by fun_prop))
  have hζ : ∀ bc : Z × Y', ζ bc = η' (x', bc.2) := fun bc ↦ by
    simp only [ζ, Kernel.prodMkLeft_apply, Kernel.comap_apply]
  simp only [hζ] at hmeas
  exact lintegral_lintegral_swap hmeas.aemeasurable

/-- **Finite-dimensional laws of the planar heat semigroup.** The finite-time law of the planar heat
semigroup started from `z` is the law of `(𝓑¹_{tᵢ} + i 𝓑²_{tᵢ})ᵢ` for independent one-dimensional
heat-semigroup samples `𝓑¹` from `Re z` and `𝓑²` from `Im z`. -/
theorem finiteTimeKernel_planarHeatSemigroup {n : ℕ} (times : FiniteOrderedTimes n) (z : ℂ) :
    SubMarkovKernelSemigroup.finiteTimeKernel planarHeatSemigroup times z =
      ((SubMarkovKernelSemigroup.finiteTimeKernel heatSemigroup times z.re).prod
        (SubMarkovKernelSemigroup.finiteTimeKernel heatSemigroup times z.im)).map
        complexCoordPathOfReIm := by
  induction n generalizing z with
  | zero =>
    simp only [SubMarkovKernelSemigroup.finiteTimeKernel_zero, Kernel.const_apply]
    rw [Measure.dirac_prod_dirac]
    ext B hB
    rw [Measure.map_apply measurable_complexCoordPathOfReIm hB, Measure.dirac_apply' _ hB,
      Measure.dirac_apply' _ (measurable_complexCoordPathOfReIm hB)]
    have h0 : complexCoordPathOfReIm (FiniteOrderedTimes.emptyPath ℝ,
        FiniteOrderedTimes.emptyPath ℝ) = FiniteOrderedTimes.emptyPath ℂ := Subsingleton.elim _ _
    classical
    rw [Set.indicator_apply, Set.indicator_apply, Set.mem_preimage, h0]
    rfl
  | succ n ih =>
    have he := Complex.measurableEquivRealProd.symm.measurable
    have := isConservative_planarHeatSemigroup.isMarkovKernel (times 0)
    have := SubMarkovKernelSemigroup.IsConservative.isMarkovKernel_finiteTimeKernel
      planarHeatSemigroup isConservative_planarHeatSemigroup times.relativeTail
    have := isConservative_heatSemigroup.isMarkovKernel (times 0)
    have := SubMarkovKernelSemigroup.IsConservative.isMarkovKernel_finiteTimeKernel
      heatSemigroup isConservative_heatSemigroup times.relativeTail
    refine (Measure.ext_iff_lintegral _).mpr fun f hf ↦ ?_
    have hL : ∫⁻ x, f x ∂(SubMarkovKernelSemigroup.finiteTimeKernel planarHeatSemigroup times z) =
        ∫⁻ a, ∫⁻ c, ∫⁻ b, ∫⁻ d, f (@Fin.cons n (fun _ ↦ ℂ)
          (Complex.measurableEquivRealProd.symm (a, c)) (complexCoordPathOfReIm (b, d)))
          ∂(SubMarkovKernelSemigroup.finiteTimeKernel heatSemigroup times.relativeTail c)
          ∂(SubMarkovKernelSemigroup.finiteTimeKernel heatSemigroup times.relativeTail a)
          ∂(gaussianReal z.im (times 0)) ∂(gaussianReal z.re (times 0)) := by
      rw [SubMarkovKernelSemigroup.finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
        Kernel.map_apply _ measurable_finCons, lintegral_map hf measurable_finCons,
        Kernel.lintegral_compProd _ _ _
          (f := fun x : ℂ × (Fin n → ℂ) ↦ f (@Fin.cons n (fun _ ↦ ℂ) x.1 x.2))
          (hf.comp measurable_finCons)]
      simp only [Kernel.prodMkLeft_apply]
      have hΦ := Measurable.lintegral_kernel_prod_right'
        (κ := SubMarkovKernelSemigroup.finiteTimeKernel planarHeatSemigroup times.relativeTail)
        (f := fun x : ℂ × (Fin n → ℂ) ↦ f (@Fin.cons n (fun _ ↦ ℂ) x.1 x.2))
        (hf.comp measurable_finCons)
      rw [planarHeatSemigroup_apply, planarGaussian, lintegral_map hΦ he, lintegral_prod]
      swap
      · exact (hΦ.comp he).aemeasurable
      refine lintegral_congr fun a ↦ lintegral_congr fun c ↦ ?_
      have hre : (Complex.measurableEquivRealProd.symm (a, c)).re = a := by
        simp [Complex.measurableEquivRealProd]
      have him : (Complex.measurableEquivRealProd.symm (a, c)).im = c := by
        simp [Complex.measurableEquivRealProd]
      have hg : Measurable fun q : (Fin n → ℂ) ↦
          f (@Fin.cons n (fun _ ↦ ℂ) (Complex.measurableEquivRealProd.symm (a, c)) q) :=
        hf.comp (measurable_finCons.comp measurable_prodMk_left)
      rw [ih, lintegral_map hg measurable_complexCoordPathOfReIm, hre, him, lintegral_prod]
      exact (hg.comp measurable_complexCoordPathOfReIm).aemeasurable
    have hR : ∫⁻ x, f x ∂(((SubMarkovKernelSemigroup.finiteTimeKernel heatSemigroup times
          z.re).prod (SubMarkovKernelSemigroup.finiteTimeKernel heatSemigroup times z.im)).map
          complexCoordPathOfReIm) =
        ∫⁻ a, ∫⁻ c, ∫⁻ b, ∫⁻ d, f (complexCoordPathOfReIm
          (@Fin.cons n (fun _ ↦ ℝ) a b, @Fin.cons n (fun _ ↦ ℝ) c d))
          ∂(SubMarkovKernelSemigroup.finiteTimeKernel heatSemigroup times.relativeTail c)
          ∂(SubMarkovKernelSemigroup.finiteTimeKernel heatSemigroup times.relativeTail a)
          ∂(gaussianReal z.im (times 0)) ∂(gaussianReal z.re (times 0)) := by
      rw [lintegral_map hf measurable_complexCoordPathOfReIm,
        SubMarkovKernelSemigroup.finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
        Kernel.map_apply _ measurable_finCons, Kernel.map_apply _ measurable_finCons,
        Measure.map_prod_map _ _ measurable_finCons measurable_finCons,
        lintegral_map _ (measurable_finCons.prodMap measurable_finCons),
        lintegral_prod_compProd_apply]
      · simp only [Kernel.prodMkLeft_apply, heatSemigroup_apply, Prod.map]
      all_goals first
        | exact (hf.comp measurable_complexCoordPathOfReIm).comp
            (measurable_finCons.prodMap measurable_finCons)
        | exact hf.comp measurable_complexCoordPathOfReIm
    rw [hL, hR]
    simp only [complexCoordPathOfReIm_cons]

/-- The finite-set laws of the planar heat semigroup are the products of those of the
one-dimensional heat semigroup, read on `ℂ`. -/
theorem finiteSetKernel_planarHeatSemigroup (I : Finset ℝ≥0) (z : ℂ) :
    SubMarkovKernelSemigroup.finiteSetKernel planarHeatSemigroup I z =
      ((SubMarkovKernelSemigroup.finiteSetKernel heatSemigroup I z.re).prod
        (SubMarkovKernelSemigroup.finiteSetKernel heatSemigroup I z.im)).map
        complexCoordPathOfReIm := by
  have hσ := SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet (α := ℝ) I
  have := SubMarkovKernelSemigroup.IsConservative.isMarkovKernel_finiteTimeKernel
    heatSemigroup isConservative_heatSemigroup (SubMarkovKernelSemigroup.finiteSetTimes I)
  rw [SubMarkovKernelSemigroup.finiteSetKernel_eq_map,
    Kernel.map_apply _ (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I),
    SubMarkovKernelSemigroup.finiteSetKernel_eq_map, Kernel.map_apply _ hσ, Kernel.map_apply _ hσ, finiteTimeKernel_planarHeatSemigroup,
    Measure.map_map (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I)
      measurable_complexCoordPathOfReIm,
    Measure.map_prod_map _ _ hσ hσ, Measure.map_map measurable_complexCoordPathOfReIm
      (hσ.prodMap hσ)]
  rfl

theorem measurable_finsetEvaluation' {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] (I : Finset ℝ≥0) :
    Measurable (ContinuousPath.finsetEvaluation (alpha := α) I) :=
  measurable_pi_iff.mpr fun t ↦ ContinuousPath.measurable_coordinateProcess (alpha := α) (t : ℝ≥0)

/-- The finite-dimensional laws of `planarBrownianMotion` are those of the planar heat semigroup. -/
theorem planarBrownianMotion_map_finsetEvaluation (I : Finset ℝ≥0) :
    planarBrownianMotion.map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel planarHeatSemigroup I := by
  ext z : 1
  have hfun : ContinuousPath.finsetEvaluation I ∘ complexPathOfReIm =
      complexCoordPathOfReIm ∘ Prod.map (ContinuousPath.finsetEvaluation I)
        (ContinuousPath.finsetEvaluation I) := by
    funext p t
    apply Complex.ext <;> simp [complexCoordPathOfReIm, complexPathOfReIm,
      Complex.measurableEquivRealProd, ContinuousPath.finiteEvaluation]
  have hR := measurable_finsetEvaluation' (α := ℝ) I
  rw [Kernel.map_apply _ (measurable_finsetEvaluation' I), planarBrownianMotion_apply,
    Measure.map_map (measurable_finsetEvaluation' I) measurable_complexPathOfReIm, hfun,
    ← Measure.map_map measurable_complexCoordPathOfReIm (hR.prodMap hR),
    ← Measure.map_prod_map _ _ hR hR, ← Kernel.map_apply _ hR, ← Kernel.map_apply _ hR,
    brownianMotion_map_finsetEvaluation, finiteSetKernel_planarHeatSemigroup]

/-- **Planar Brownian motion is the continuous-path Markov process of the planar heat semigroup.**
-/
theorem planarBrownianMotion_eq_continuousProcess :
    planarBrownianMotion = SubMarkovKernelSemigroup.IsConservative.continuousProcess
      planarHeatSemigroup isConservative_planarHeatSemigroup :=
  SubMarkovKernelSemigroup.IsConservative.eq_continuousProcess_of_map_finiteEvaluation
    planarHeatSemigroup isConservative_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup
    planarBrownianMotion planarBrownianMotion_map_finsetEvaluation

end FiniteDimensional

end HarmonicBalls
