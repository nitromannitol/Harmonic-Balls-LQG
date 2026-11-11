import HarmonicBalls.Proofs.Potential.GeneralDomainGreenProductIntegrability

/-!
# Source truncation of transposed Green potentials

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter
open scoped Topology

/-- Source truncation preserves integrability, and converges almost everywhere and in L1.
The kernel order is the literal source-observer order. -/
theorem transposedGreen_source_truncation {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ∀ᵐ y ∂ν, y ∈ V)
    (K : ℕ → Set ℂ) (hK : ∀ n, MeasurableSet (K n))
    (hmono : Monotone K) (hcover : V ⊆ ⋃ n, K n) :
    (∀ n, IntegrableOn (fun x => ∫ y in K n, greenFunction V y x ∂ν) V) ∧
    (∀ᵐ x ∂(volume.restrict V),
      Integrable (fun y => greenFunction V y x) ν ∧
      (∀ n, IntegrableOn (fun y => greenFunction V y x) (K n) ν) ∧
      Tendsto (fun n => ∫ y in K n, greenFunction V y x ∂ν) atTop
        (𝓝 (∫ y, greenFunction V y x ∂ν))) ∧
    Tendsto (fun n => ∫ x in V, ‖(∫ y in K n, greenFunction V y x ∂ν) -
      (∫ y, greenFunction V y x ∂ν)‖) atTop (𝓝 0) := by
  have hp := generalDomain_green_integrable_product_volume hV hVb hν
  have hfull := integrableOn_generalDomain_transposedGreenPotential hV hVb hν
  have hint (n : ℕ) : IntegrableOn (fun x => ∫ y in K n, greenFunction V y x ∂ν) V := by
    have hprod : Integrable (fun p : ℂ × ℂ => greenFunction V p.1 p.2)
        ((ν.restrict (K n)).prod (volume.restrict V)) :=
      hp.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
    exact hprod.integral_prod_right
  have hpoint : ∀ᵐ x ∂(volume.restrict V),
      Integrable (fun y => greenFunction V y x) ν ∧
      (∀ n, IntegrableOn (fun y => greenFunction V y x) (K n) ν) ∧
      Tendsto (fun n => ∫ y in K n, greenFunction V y x ∂ν) atTop
        (𝓝 (∫ y, greenFunction V y x ∂ν)) := by
    filter_upwards [hp.prod_left_ae] with x hx
    refine ⟨hx, fun n => hx.mono_measure Measure.restrict_le_self, ?_⟩
    have hc : ∀ᵐ y ∂ν, ∃ N, ∀ n ≥ N, y ∈ K n := by
      filter_upwards [hν] with y hy
      obtain ⟨N, hN⟩ := mem_iUnion.mp (hcover hy)
      exact ⟨N, fun n hn => hmono hn hN⟩
    have hd := tendsto_integral_of_dominated_convergence
      (μ := ν) (F := fun n => (K n).indicator (fun y => greenFunction V y x))
      (f := fun y => greenFunction V y x) (fun y => ‖greenFunction V y x‖)
      (fun n => hx.aestronglyMeasurable.indicator (hK n)) hx.norm
      (fun n => Filter.Eventually.of_forall fun y => by
        by_cases hy : y ∈ K n <;> simp [hy])
      (hc.mono fun y hy => by
        obtain ⟨N, hN⟩ := hy
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop N] with n hn
        simp [hN n hn])
    simpa only [integral_indicator (hK _)] using hd
  refine ⟨hint, hpoint, ?_⟩
  have hbound : Integrable (fun x => 2 * (∫ y, greenFunction V y x ∂ν))
      (volume.restrict V) := hfull.const_mul 2
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict V) (fun x => 2 * (∫ y, greenFunction V y x ∂ν))
    (fun n => ((hint n).sub hfull).norm.aestronglyMeasurable) hbound
    (fun n => by
      filter_upwards [hp.prod_left_ae] with x hx
      have hn : 0 ≤ ∫ y in K n, greenFunction V y x ∂ν :=
        integral_nonneg fun y => greenFunction_nonneg hVb y x
      have hf : 0 ≤ ∫ y, greenFunction V y x ∂ν :=
        integral_nonneg fun y => greenFunction_nonneg hVb y x
      have hle : (∫ y in K n, greenFunction V y x ∂ν) ≤
          ∫ y, greenFunction V y x ∂ν := by
        exact integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall fun y => greenFunction_nonneg hVb y x) hx
      change ‖‖(∫ y in K n, greenFunction V y x ∂ν) -
        (∫ y, greenFunction V y x ∂ν)‖‖ ≤ _
      rw [norm_norm, Real.norm_eq_abs]
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      linarith)
    (hpoint.mono fun x hx => by
      simpa using (hx.2.2.sub tendsto_const_nhds).norm)
  simpa using hlim


end HarmonicBalls
