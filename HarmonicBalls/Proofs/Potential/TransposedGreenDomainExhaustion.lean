import HarmonicBalls.Proofs.Potential.GreenDomainExhaustion
import HarmonicBalls.Proofs.Potential.GeneralDomainGreenProductIntegrability
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Transposed Green potentials along open exhaustions

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter
open scoped Topology

/-- A finite source's literal transposed Green potentials converge almost
 everywhere on a bounded open domain along any monotone open exhaustion. -/
theorem ae_tendsto_transposedGreenPotential_of_exhaustion
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hcover : (⋃ n, V n) = U) {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ y ∂ν, y ∈ U) :
    ∀ᵐ x ∂(volume.restrict U),
      Tendsto (fun n => ∫ y, greenFunction (V n) y x ∂ν) atTop
        (𝓝 (∫ y, greenFunction U y x ∂ν)) := by
  have hsub (n : ℕ) : V n ⊆ U := by rw [← hcover]; exact subset_iUnion V n
  have hp := generalDomain_green_integrable_product_volume hU hUb hν
  filter_upwards [hp.swap.prod_right_ae, ae_restrict_mem hU.measurableSet] with x hx hxU
  apply tendsto_integral_of_dominated_convergence (fun y => greenFunction U y x)
  · intro n
    exact ((measurable_greenFunction_uncurry (hopen n)).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · exact hx
  · intro n
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (greenFunction_nonneg (hUb.subset (hsub n)) y x)]
    exact Section6.greenFunction_le_of_subset (hsub n) hUb y x
  · filter_upwards [hν] with y hy
    by_cases h : y = x
    · subst y
      simpa only [greenFunction_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · exact tendsto_greenFunction_of_exhaustion V hopen hmono hU hUb hcover hy hxU h

/-- The same exhaustion converges in integral norm on the domain. -/
theorem tendsto_integral_norm_transposedGreenPotential_sub_of_exhaustion
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hcover : (⋃ n, V n) = U) {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ y ∂ν, y ∈ U) :
    Tendsto (fun n => ∫ x in U, ‖(∫ y, greenFunction (V n) y x ∂ν) -
      (∫ y, greenFunction U y x ∂ν)‖) atTop (𝓝 0) := by
  have hsub (n : ℕ) : V n ⊆ U := by rw [← hcover]; exact subset_iUnion V n
  have hp := generalDomain_green_integrable_product_volume hU hUb hν
  have hpn (n : ℕ) : Integrable (fun p : ℂ × ℂ => greenFunction (V n) p.1 p.2)
      (ν.prod (volume.restrict U)) := by
    apply hp.mono_nonneg (measurable_greenFunction_uncurry (hopen n)).aestronglyMeasurable
    · exact Eventually.of_forall fun p => greenFunction_nonneg (hUb.subset (hsub n)) p.1 p.2
    · exact Eventually.of_forall fun p => Section6.greenFunction_le_of_subset (hsub n) hUb p.1 p.2
  have hi := hp.integral_prod_right
  have hin (n : ℕ) := (hpn n).integral_prod_right
  have hlim := ae_tendsto_transposedGreenPotential_of_exhaustion V hopen hmono hU hUb hcover hν
  have hb (n : ℕ) : ∀ᵐ x ∂(volume.restrict U),
      ‖(∫ y, greenFunction (V n) y x ∂ν) - (∫ y, greenFunction U y x ∂ν)‖ ≤
        2 * (∫ y, greenFunction U y x ∂ν) := by
    filter_upwards [(hpn n).swap.prod_right_ae, hp.swap.prod_right_ae] with x hxn hx
    have hnon : 0 ≤ ∫ y, greenFunction (V n) y x ∂ν :=
      integral_nonneg (greenFunction_nonneg (hUb.subset (hsub n)) · x)
    have hle : (∫ y, greenFunction (V n) y x ∂ν) ≤ ∫ y, greenFunction U y x ∂ν :=
      integral_mono_ae hxn hx (Eventually.of_forall fun y =>
        Section6.greenFunction_le_of_subset (hsub n) hUb y x)
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith
  have ht := tendsto_integral_of_dominated_convergence
    (fun x => 2 * (∫ y, greenFunction U y x ∂ν))
    (fun n => ((hin n).sub hi).aestronglyMeasurable.norm)
    (hi.const_mul 2)
    (fun n => by filter_upwards [hb n] with x hx; simpa only [Pi.sub_apply, norm_norm] using hx)
    (by filter_upwards [hlim] with x hx
        simpa only [Pi.sub_apply, sub_self, norm_zero] using (hx.sub tendsto_const_nhds).norm)
  simpa only [Pi.sub_apply, sub_self, norm_zero, integral_zero] using ht

#print axioms ae_tendsto_transposedGreenPotential_of_exhaustion
#print axioms tendsto_integral_norm_transposedGreenPotential_sub_of_exhaustion
end HarmonicBalls
