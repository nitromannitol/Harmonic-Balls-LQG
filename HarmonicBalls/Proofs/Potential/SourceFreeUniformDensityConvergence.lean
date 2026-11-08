import HarmonicBalls.Proofs.Potential.SigmaFiniteDensitySourceFreeHarmonicity

/-! # Local uniform convergence of source-free Green potentials

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
The source is the first argument of the Green kernel.
-/

namespace HarmonicBalls
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology

/-- A compact observer set admits a common L¹ bound for densities vanishing
almost everywhere in its source-free neighborhood. -/
theorem sigmaFinite_source_free_density_green_bound
    {V U L : Set ℂ} {ν : Measure ℂ} [SigmaFinite ν]
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hν : ∀ᵐ y ∂ν, y ∈ V)
    (hU : IsOpen U) (hL : IsCompact L) (hLU : L ⊆ U) (hUV : U ⊆ V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℂ → ℝ), Measurable f → Integrable f ν →
      (∀ᵐ y ∂ν, y ∈ U → f y = 0) → ∀ x ∈ L,
      |∫ y, f y * greenFunction V y x ∂ν| ≤ C * ∫ y, |f y| ∂ν := by
  obtain ⟨C, hC⟩ := exists_uniform_bound_transposed_green_of_source_free
    hVb hU hL hLU (hLU.trans hUV)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro f hf hfi hz x hx
  have hi := (sigmaFinite_integrable_density_transposedGreen_source_free
    hV hVb hν hU hUV hf hfi hz).1 x (hLU hx)
  calc
    |∫ y, f y * greenFunction V y x ∂ν| ≤ ∫ y, ‖f y * greenFunction V y x‖ ∂ν := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun y => f y * greenFunction V y x)
    _ ≤ ∫ y, max C 0 * |f y| ∂ν := by
      apply integral_mono_ae hi.norm (hfi.norm.const_mul (max C 0))
      filter_upwards [hν, hz] with y hy hv
      by_cases hyU : y ∈ U
      · simp only [hv hyU, zero_mul, norm_zero, mul_zero, le_refl]
      · have hb := (hC y ⟨hy, hyU⟩ x hx).trans (le_max_left C 0)
        simpa only [norm_mul, Real.norm_eq_abs, mul_comm] using
          mul_le_mul_of_nonneg_left hb (abs_nonneg (f y))
    _ = max C 0 * ∫ y, |f y| ∂ν := integral_const_mul _ _

/-- L¹ convergence of source-free densities gives uniform convergence of their
actual transposed Green potentials on every compact observer set. -/
theorem sigmaFinite_source_free_density_green_local_uniform
    {V U L : Set ℂ} {ν : Measure ℂ} [SigmaFinite ν]
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hν : ∀ᵐ y ∂ν, y ∈ V)
    (hU : IsOpen U) (hL : IsCompact L) (hLU : L ⊆ U) (hUV : U ⊆ V)
    (f : ℕ → ℂ → ℝ) (g : ℂ → ℝ)
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hf : ∀ n, Integrable (f n) ν) (hg : Integrable g ν)
    (hfz : ∀ n, ∀ᵐ y ∂ν, y ∈ U → f n y = 0)
    (hgz : ∀ᵐ y ∂ν, y ∈ U → g y = 0)
    (hlim : Tendsto (fun n => ∫ y, |f n y - g y| ∂ν) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ L,
      |(∫ y, f n y * greenFunction V y x ∂ν) -
        (∫ y, g y * greenFunction V y x ∂ν)| < ε := by
  obtain ⟨C, _, hb⟩ := sigmaFinite_source_free_density_green_bound hV hVb hν hU hL hLU hUV
  have ht : Tendsto (fun n => C * ∫ y, |f n y - g y| ∂ν) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hlim
  intro ε hε
  filter_upwards [(tendsto_order.1 ht).2 ε hε] with n hn x hx
  have hi := (sigmaFinite_integrable_density_transposedGreen_source_free
    hV hVb hν hU hUV (hfm n) (hf n) (hfz n)).1 x (hLU hx)
  have hj := (sigmaFinite_integrable_density_transposedGreen_source_free
    hV hVb hν hU hUV hgm hg hgz).1 x (hLU hx)
  have hz : ∀ᵐ y ∂ν, y ∈ U → f n y - g y = 0 := by
    filter_upwards [hfz n, hgz] with y hy hz hyU
    simp only [hy hyU, hz hyU, sub_self]
  have heq : (∫ y, f n y * greenFunction V y x ∂ν) -
      (∫ y, g y * greenFunction V y x ∂ν) =
      ∫ y, (f n y - g y) * greenFunction V y x ∂ν := by
    rw [← integral_sub hi hj]
    congr 1
    funext y
    ring
  rw [heq]
  exact lt_of_le_of_lt (hb (fun y => f n y - g y) ((hfm n).sub hgm)
    ((hf n).sub hg) hz x hx) hn

#print axioms sigmaFinite_source_free_density_green_bound
#print axioms sigmaFinite_source_free_density_green_local_uniform
end HarmonicBalls
