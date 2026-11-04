import HarmonicBalls.Steps.Sec11.PinchGreenMeasurable
import HarmonicBalls.Proofs.Sec11.PinchUnnormalizedKernel
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-! # Joint measurability of translated random measures

The random measure is represented by an s-finite kernel. Its translation by a
variable center is a measurable measure-valued function. -/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

/-- A random measure represented by an s-finite kernel can be translated by
a variable point in a jointly measurable way. -/
theorem measurable_kernel_map_sub
    {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℂ) [IsSFiniteKernel κ] :
    Measurable (fun p : Ω × ℂ => (κ p.1).map (fun y : ℂ => y - p.2)) := by
  let η : Kernel (Ω × ℂ) ℂ := κ.comap Prod.fst measurable_fst
  have : IsSFiniteKernel η := inferInstance
  apply Measure.measurable_of_measurable_coe
  intro S hS
  have ht : MeasurableSet {p : (Ω × ℂ) × ℂ | p.2 - p.1.2 ∈ S} :=
    hS.preimage (measurable_snd.sub (measurable_snd.comp measurable_fst))
  have hm := Kernel.measurable_kernel_prodMk_left (κ := η) ht
  convert hm using 1
  ext p
  rw [Measure.map_apply (show Measurable (fun y : ℂ => y - p.2) from by fun_prop) hS]
  rfl

/-- Recentering a measure translates an annular Green integral, including
its infinite diagonal value. -/
theorem annulusGreenIntegral_map_sub (μ : Measure ℂ) (z x : ℂ) (a b : ℝ) :
    (∫⁻ y in annulus 0 a b, (if y = x then ∞ else
      ENNReal.ofReal (greenFunction (ball 0 b) x y))
      ∂(μ.map (fun y : ℂ => y - z))) =
    ∫⁻ y in annulus z a b, (if y = x + z then ∞ else
      ENNReal.ofReal (greenFunction (ball z b) (x + z) y)) ∂μ := by
  have hA : MeasurableSet (annulus 0 a b) :=
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hf : Measurable (fun y : ℂ => if y = x then ∞ else
      ENNReal.ofReal (greenFunction (ball 0 b) x y)) :=
    Measurable.ite (measurableSet_singleton x) measurable_const
      ((measurable_greenFunction isOpen_ball x).ennreal_ofReal)
  have hpre : (fun y : ℂ => y - z) ⁻¹' annulus 0 a b = annulus z a b := by
    ext y
    simp only [annulus, mem_preimage, mem_sdiff, mem_ball, mem_closedBall, dist_eq_norm,
      sub_zero]
  rw [setLIntegral_map hA hf (by fun_prop), hpre]
  apply lintegral_congr_ae
  filter_upwards [] with y
  rw [greenFunction_ball_translate z (x + z) y b]
  simp only [add_sub_cancel_right, sub_eq_iff_eq_add]

/-- Recentering a measure translates the annular Green-potential supremum. -/
theorem annulusGreenPotentialSup_map_sub (μ : Measure ℂ) (z : ℂ) (a b : ℝ) :
    annulusGreenPotentialSup (μ.map (fun y : ℂ => y - z)) 0 a b =
      annulusGreenPotentialSup μ z a b := by
  have hmem (x : ℂ) : x + z ∈ annulus z a b ↔ x ∈ annulus 0 a b := by
    simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, dist_eq_norm,
      add_sub_cancel_right, sub_zero]
  unfold annulusGreenPotentialSup
  simp_rw [annulusGreenIntegral_map_sub μ z]
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun hx => ?_
    exact le_iSup_of_le (x + z) (le_iSup_of_le ((hmem x).2 hx) le_rfl)
  · refine iSup_le fun y => iSup_le fun hy => ?_
    have hx : y - z ∈ annulus 0 a b := (hmem (y - z)).1 (by simpa using hy)
    apply le_iSup_of_le (y - z)
    apply le_iSup_of_le hx
    simp only [sub_add_cancel]
    exact le_rfl

/-- Annular Green-potential suprema of the recentered measure are jointly
measurable in the random sample and the center. -/
theorem measurable_kernel_recentered_annulusGreenPotentialSup
    {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℂ) [IsSFiniteKernel κ] (a b : ℝ) :
    Measurable (fun p : Ω × ℂ => annulusGreenPotentialSup
      ((κ p.1).map (fun y : ℂ => y - p.2)) 0 a b) :=
  (measurable_annulusGreenPotentialSup 0 a b).comp (measurable_kernel_map_sub κ)

/-- The annular Green-potential supremum is jointly measurable in the
sample and its moving center. -/
theorem measurable_kernel_annulusGreenPotentialSup
    {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℂ) [IsSFiniteKernel κ] (a b : ℝ) :
    Measurable (fun p : Ω × ℂ => annulusGreenPotentialSup (κ p.1) p.2 a b) := by
  convert measurable_kernel_recentered_annulusGreenPotentialSup κ a b using 1
  ext p
  exact (annulusGreenPotentialSup_map_sub (κ p.1) p.2 a b).symm

/-- Mass of a rescaled open set is jointly measurable in the sample and
center for an s-finite random-measure kernel. -/
theorem measurable_kernel_rescaledSet_mass
    {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
    (U : Set ℂ) (hU : IsOpen U) {r : ℝ} (hr : r ≠ 0) :
    Measurable (fun p : Ω × ℂ => κ p.1 (rescaledSet U r p.2)) := by
  have hU0 : MeasurableSet (rescaledSet U r 0) :=
    (isOpen_rescaledSet hU hr 0).measurableSet
  have hpre (z : ℂ) : (fun y : ℂ => y - z) ⁻¹' rescaledSet U r 0 = rescaledSet U r z := by
    ext y
    simp only [rescaledSet, mem_preimage, mem_image, add_zero]
    constructor
    · rintro ⟨x, hx, heq⟩
      exact ⟨x, hx, eq_sub_iff_add_eq.mp heq⟩
    · rintro ⟨x, hx, heq⟩
      exact ⟨x, hx, eq_sub_iff_add_eq.mpr heq⟩
  have hm := (Measure.measurable_coe hU0).comp (measurable_kernel_map_sub κ)
  convert hm using 1
  ext p
  change κ p.1 (rescaledSet U r p.2) =
    ((κ p.1).map (fun y : ℂ => y - p.2)) (rescaledSet U r 0)
  rw [Measure.map_apply (show Measurable (fun y : ℂ => y - p.2) from by fun_prop) hU0, hpre]

#print axioms annulusGreenPotentialSup_map_sub
#print axioms measurable_kernel_annulusGreenPotentialSup
#print axioms measurable_kernel_rescaledSet_mass
#print axioms measurable_kernel_map_sub
#print axioms measurable_kernel_recentered_annulusGreenPotentialSup

end HarmonicBalls
