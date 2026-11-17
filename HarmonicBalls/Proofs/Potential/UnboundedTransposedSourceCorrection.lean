import HarmonicBalls.Proofs.Potential.GeneralDomainObservationCorrection

/-!
# Conditional correction for unbounded-domain Green potentials

A measurable, locally uniformly bounded harmonic family representing the
unbounded-domain minorants yields a harmonic correction of source potentials.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace Filter

/-- Integrating a harmonic family of actual unbounded-domain minorants compares
literal transposed Green potentials at every observer satisfying the stated
integrability and atom conditions. -/
theorem exists_harmonic_unbounded_transposed_correction_of_minorant_family
    {U V K : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hK : IsCompact K) (hKV : K ⊆ V) (hVU : V ⊆ U)
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ν Kᶜ = 0)
    {F : ℂ → ℂ → ℝ} (hFm : Measurable (Function.uncurry F))
    (hFh : ∀ y, HarmonicOnNhd (F y) V)
    (hFb : ∀ L : Set ℂ, IsCompact L → L ⊆ V →
      ∃ C : ℝ, ∀ y, ∀ x ∈ L, |F y x| ≤ C)
    (hFag : ∀ y ∈ K, ∀ x ∈ V,
      (greatestHarmonicMinorant U (newtonKernelEReal y) x).toReal = F y x) :
    ∃ H : ℂ → ℝ, HarmonicOnNhd H V ∧
      ∀ x ∈ V, ν {x} = 0 → Integrable (fun y => newtonKernel y x) ν →
        Integrable (fun y => greenFunction V y x) ν →
        Integrable (fun y => greenFunction U y x) ν →
        (∫ y, greenFunction U y x ∂ν) =
          (∫ y, greenFunction V y x ∂ν) + H x := by
  have hae : ∀ᵐ y ∂ν, y ∈ K := by rw [ae_iff]; exact hν
  have hcont : ContinuousOn (fun x => ∫ y, F y x ∂ν) V := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hV x hx
    have hsub : closedBall x (δ / 2) ⊆ V :=
      (closedBall_subset_ball (by linarith)).trans hδsub
    obtain ⟨C, hC⟩ := hFb _ (isCompact_closedBall x (δ / 2)) hsub
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => max C 0)
    · exact Filter.Eventually.of_forall fun w =>
        (hFm.comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℂ => w)))).aestronglyMeasurable
    · filter_upwards [closedBall_mem_nhds x (by linarith : 0 < δ / 2)] with w hw
      exact Filter.Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs] using (hC y w hw).trans (le_max_left C 0)
    · exact integrable_const _
    · exact Filter.Eventually.of_forall fun y => ((hFh y x hx).1.continuousAt.tendsto)
  have hharm : HarmonicOnNhd (fun x => ∫ y, F y x ∂ν) V := by
    apply Section6.harmonicOnNhd_integral_of_circle_bounds hV hFh hFm hcont
    intro c r hr hsub
    obtain ⟨C, hC⟩ := hFb _ (isCompact_sphere c r) (sphere_subset_closedBall.trans hsub)
    exact ⟨C, hC⟩
  obtain ⟨H, hH, hHid⟩ :=
    exists_harmonic_generalDomain_transposed_correction_pointwise hV hVb hK hKV hν
  refine ⟨fun x => H x - ∫ y, F y x ∂ν, hH.sub hharm, ?_⟩
  intro x hx hnx hi hVi hUi
  have hne : ∀ᵐ y ∂ν, y ≠ x := by rw [ae_iff]; simpa using hnx
  have heq : (fun y => greenFunction U y x) =ᵐ[ν] fun y => newtonKernel y x - F y x := by
    filter_upwards [hae, hne] with y hy hyx
    rw [greenFunction, ite_eq_left ⟨hVU (hKV hy), hVU hx, hyx⟩, hFag y hy x hx]
  have hFi : Integrable (fun y => F y x) ν := by
    have heq' : (fun y => F y x) =ᵐ[ν] fun y => newtonKernel y x - greenFunction U y x := by
      filter_upwards [heq] with y hy
      linarith
    exact (hi.sub hUi).congr heq'.symm
  have hU : (∫ y, greenFunction U y x ∂ν) =
      (∫ y, newtonKernel y x ∂ν) - ∫ y, F y x ∂ν := by
    rw [integral_congr_ae heq, integral_sub hi hFi]
  have hVeq := hHid x hx hnx hi hVi
  have hplane : greenPotential univ ν x = ∫ y, newtonKernel y x ∂ν := by
    simp only [greenPotential, greenFunction_univ_eq_newtonKernel, newtonKernel_comm]
  rw [hplane] at hVeq
  linarith

end HarmonicBalls
