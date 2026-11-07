import HarmonicBalls.Proofs.Potential.TransposedTruncationLocalUniform
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Source-free weighted transposed Green potentials

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
The source is the first argument of the Green kernel.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ENNReal

/-- An integrable source density gives an integrable kernel slice at every
source-free observer. -/
theorem integrable_weighted_transposed_green_of_source_free
    {V U : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν] {f : ℂ → ℝ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hνV : ν Vᶜ = 0)
    (hU : IsOpen U) (hUV : U ⊆ V) (hνU : ν U = 0)
    (hf : Integrable f ν) {x : ℂ} (hx : x ∈ U) :
    Integrable (fun y => f y * greenFunction V y x) ν := by
  obtain ⟨C, hC⟩ := exists_uniform_bound_transposed_green_of_source_free
    hVb hU isCompact_singleton (singleton_subset_iff.mpr hx)
    (singleton_subset_iff.mpr (hUV hx))
  have hae : ∀ᵐ y ∂ν, y ∈ V \ U := by
    rw [ae_iff]
    apply measure_mono_null (show (V \ U)ᶜ ⊆ Vᶜ ∪ U from by
      intro y hy
      by_cases hv : y ∈ V
      · right
        by_contra hu
        exact hy ⟨hv, hu⟩
      · exact Or.inl hv)
    exact measure_union_null hνV hνU
  apply (hf.norm.const_mul (max C 0)).mono'
    (hf.aestronglyMeasurable.mul ((measurable_greenFunction_uncurry hV).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  filter_upwards [hae] with y hy
  have hb : ‖greenFunction V y x‖ ≤ max C 0 := by
    simpa only [Real.norm_eq_abs] using (hC y hy x (mem_singleton x)).trans (le_max_left C 0)
  simpa [Function.comp_def, norm_mul, mul_comm] using
    mul_le_mul_of_nonneg_left hb (norm_nonneg (f y))

/-- A signed integrable density gives a harmonic source-free transposed potential. -/
theorem harmonicOnNhd_weighted_transposed_green_of_source_free
    {V U : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν] {f : ℂ → ℝ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hνV : ν Vᶜ = 0)
    (hU : IsOpen U) (hUV : U ⊆ V) (hνU : ν U = 0)
    (hf : Integrable f ν) :
    HarmonicOnNhd (fun x => ∫ y, f y * greenFunction V y x ∂ν) U := by
  let p : ℂ → ℝ := fun y => max (f y) 0
  let m : ℂ → ℝ := fun y => max (-f y) 0
  have hp : Integrable p ν := hf.pos_part
  have hm : Integrable m ν := hf.neg_part
  let μp := ν.withDensity (fun y => ENNReal.ofReal (p y))
  let μm := ν.withDensity (fun y => ENNReal.ofReal (m y))
  let : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hp.2
  let : IsFiniteMeasure μm := isFiniteMeasure_withDensity_ofReal hm.2
  have hpV : μp Vᶜ = 0 := withDensity_absolutelyContinuous _ _ hνV
  have hmV : μm Vᶜ = 0 := withDensity_absolutelyContinuous _ _ hνV
  have hpU : μp U = 0 := withDensity_absolutelyContinuous _ _ hνU
  have hmU : μm U = 0 := withDensity_absolutelyContinuous _ _ hνU
  have hh := (harmonicOnNhd_transposed_greenIntegral_of_finite_source hV hVb hpV hU hUV hpU).sub
    (harmonicOnNhd_transposed_greenIntegral_of_finite_source hV hVb hmV hU hUV hmU)
  have heq : ∀ x ∈ U, (∫ y, f y * greenFunction V y x ∂ν) =
      ((fun x => ∫ y, greenFunction V y x ∂μp) -
       (fun x => ∫ y, greenFunction V y x ∂μm)) x := by
    intro x hx
    have hip := integrable_weighted_transposed_green_of_source_free hV hVb hνV hU hUV hνU hp hx
    have him := integrable_weighted_transposed_green_of_source_free hV hVb hνV hU hUV hνU hm hx
    have ep : (∫ y, greenFunction V y x ∂μp) = ∫ y, p y * greenFunction V y x ∂ν := by
      simpa only [μp, ENNReal.toReal_ofReal (le_max_right _ _), p, smul_eq_mul] using
        (integral_withDensity_eq_integral_toReal_smul₀ hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
          (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (fun y => greenFunction V y x))
    have em : (∫ y, greenFunction V y x ∂μm) = ∫ y, m y * greenFunction V y x ∂ν := by
      simpa only [μm, ENNReal.toReal_ofReal (le_max_right _ _), m, smul_eq_mul] using
        (integral_withDensity_eq_integral_toReal_smul₀ hm.aestronglyMeasurable.aemeasurable.ennreal_ofReal
          (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (fun y => greenFunction V y x))
    change (∫ y, f y * greenFunction V y x ∂ν) =
      (∫ y, greenFunction V y x ∂μp) - (∫ y, greenFunction V y x ∂μm)
    rw [ep, em, ← integral_sub hip him]
    apply integral_congr_ae
    filter_upwards with y
    dsimp [p, m]
    have h : max (f y) 0 - max (-f y) 0 = f y := by
      rcases le_total 0 (f y) with h | h
      · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
      · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
    rw [← sub_mul, h]

  intro x hx
  apply (harmonicAt_congr_nhds ?_).2 (hh x hx)
  filter_upwards [hU.mem_nhds hx] with z hz
  exact heq z hz

/-- A common kernel bound controls signed potentials by the L¹ norm of their density. -/
theorem weighted_transposed_green_source_free_bound
    {V U L : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hU : IsOpen U) (hL : IsCompact L) (hLU : L ⊆ U) (hUV : U ⊆ V)
    (hνV : ν Vᶜ = 0) (hνU : ν U = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℂ → ℝ), Integrable f ν → ∀ x ∈ L,
      |∫ y, f y * greenFunction V y x ∂ν| ≤ C * ∫ y, |f y| ∂ν := by
  obtain ⟨C, hC⟩ := exists_uniform_bound_transposed_green_of_source_free
    hVb hU hL hLU (hLU.trans hUV)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro f hf x hx
  have hae : ∀ᵐ y ∂ν, y ∈ V \ U := by
    rw [ae_iff]
    apply measure_mono_null (show (V \ U)ᶜ ⊆ Vᶜ ∪ U from by
      intro y hy
      by_cases hv : y ∈ V
      · right
        by_contra hu
        exact hy ⟨hv, hu⟩
      · exact Or.inl hv)
    exact measure_union_null hνV hνU
  have hi := integrable_weighted_transposed_green_of_source_free
    hV hVb hνV hU hUV hνU hf (hLU hx)
  calc
    |∫ y, f y * greenFunction V y x ∂ν| ≤ ∫ y, ‖f y * greenFunction V y x‖ ∂ν := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun y => f y * greenFunction V y x)
    _ ≤ ∫ y, max C 0 * |f y| ∂ν := by
      apply integral_mono_ae hi.norm (hf.norm.const_mul (max C 0))
      filter_upwards [hae] with y hy
      have hb := (hC y hy x hx).trans (le_max_left C 0)
      simpa only [norm_mul, Real.norm_eq_abs, mul_comm] using
        mul_le_mul_of_nonneg_left hb (abs_nonneg (f y))
    _ = max C 0 * ∫ y, |f y| ∂ν := integral_const_mul _ _

/-- L¹ convergence of real source densities gives harmonic potentials and
uniform convergence on compact subsets of a source-free open set. -/
theorem weighted_transposed_green_L1_local_uniform
    {V U L : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hU : IsOpen U) (hL : IsCompact L) (hLU : L ⊆ U) (hUV : U ⊆ V)
    (hνV : ν Vᶜ = 0) (hνU : ν U = 0)
    (f : ℕ → ℂ → ℝ) (g : ℂ → ℝ)
    (hf : ∀ n, Integrable (f n) ν) (hg : Integrable g ν)
    (hlim : Tendsto (fun n => ∫ y, |f n y - g y| ∂ν) atTop (𝓝 0)) :
    HarmonicOnNhd (fun x => ∫ y, g y * greenFunction V y x ∂ν) U ∧
    (∀ n, HarmonicOnNhd (fun x => ∫ y, f n y * greenFunction V y x ∂ν) U) ∧
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ L,
      |(∫ y, f n y * greenFunction V y x ∂ν) -
        (∫ y, g y * greenFunction V y x ∂ν)| < ε := by
  refine ⟨harmonicOnNhd_weighted_transposed_green_of_source_free hV hVb hνV hU hUV hνU hg,
    fun n => harmonicOnNhd_weighted_transposed_green_of_source_free hV hVb hνV hU hUV hνU (hf n), ?_⟩
  obtain ⟨C, hC, hb⟩ := weighted_transposed_green_source_free_bound hV hVb hU hL hLU hUV hνV hνU
  have ht : Tendsto (fun n => C * ∫ y, |f n y - g y| ∂ν) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hlim
  intro ε hε
  filter_upwards [(tendsto_order.1 ht).2 ε hε] with n hn x hx
  have hi := integrable_weighted_transposed_green_of_source_free hV hVb hνV hU hUV hνU (hf n) (hLU hx)
  have hj := integrable_weighted_transposed_green_of_source_free hV hVb hνV hU hUV hνU hg (hLU hx)
  have heq : (∫ y, f n y * greenFunction V y x ∂ν) -
      (∫ y, g y * greenFunction V y x ∂ν) =
      ∫ y, (f n y - g y) * greenFunction V y x ∂ν := by
    rw [← integral_sub hi hj]
    congr 1
    funext y
    ring
  rw [heq]
  exact lt_of_le_of_lt (hb (fun y => f n y - g y) ((hf n).sub hg) x hx) hn

#print axioms integrable_weighted_transposed_green_of_source_free
#print axioms harmonicOnNhd_weighted_transposed_green_of_source_free
#print axioms weighted_transposed_green_source_free_bound
#print axioms weighted_transposed_green_L1_local_uniform

end HarmonicBalls
