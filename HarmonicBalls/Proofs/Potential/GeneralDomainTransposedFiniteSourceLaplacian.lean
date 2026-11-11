import HarmonicBalls.Proofs.Potential.GeneralDomainGreenProductIntegrability
import HarmonicBalls.Proofs.Potential.GeneralDomainGreenLaplacian

/-!
# Distributional Laplacian of the transposed Green potential

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian

/-- A finite source concentrated in a bounded open domain has the expected
Laplacian for its literal transposed Green potential, including atomic sources. -/
theorem hasLaplacian_generalDomain_transposedGreenPotential {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ∀ᵐ y ∂ν, y ∈ V) :
    HasLaplacian (fun x => ∫ y, greenFunction V y x ∂ν) 0 ν V := by
  refine ⟨locallyIntegrableOn_generalDomain_transposedGreenPotential hV hVb hν,
    fun φ hφ => ?_⟩
  refine ⟨integrable_zero_measure, hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1, ?_⟩
  have hΔc : Continuous (Δ φ) := continuous_laplacian_of_contDiff (hφ.1.of_le (by norm_cast))
  obtain ⟨R, hsub⟩ := hVb.subset_ball (0 : ℂ)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hΔc.continuousOn
  have hp := generalDomain_green_integrable_product_volume hV hVb hν
  have hw : Integrable (fun p : ℂ × ℂ => greenFunction V p.1 p.2 * Δ φ p.2)
      (ν.prod (volume.restrict V)) := by
    apply hp.mul_bdd (hΔc.measurable.comp measurable_snd).aestronglyMeasurable
    filter_upwards [(Measure.ae_prod_iff_ae_ae (hV.measurableSet.preimage measurable_snd)).mpr
      (Filter.Eventually.of_forall fun _ => ae_restrict_mem hV.measurableSet)] with p hp
    exact hB p.2 (ball_subset_closedBall (hsub hp))
  have hzero : ∀ x, x ∉ V → Δ φ x = 0 := fun x hx =>
    laplacian_eq_zero_of_notMem_tsupport fun h => hx (hφ.2.2 h)
  calc
    ∫ x, (∫ y, greenFunction V y x ∂ν) * Δ φ x =
        ∫ x in V, (∫ y, greenFunction V y x ∂ν) * Δ φ x := by
          symm
          exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hzero x hx])
    _ = ∫ x in V, ∫ y, greenFunction V y x * Δ φ x ∂ν := by
          apply integral_congr_ae
          filter_upwards with x
          rw [integral_mul_const]
    _ = ∫ y, (∫ x in V, greenFunction V y x * Δ φ x) ∂ν :=
          (integral_integral_swap hw).symm
    _ = ∫ y, -φ y ∂ν := by
          apply integral_congr_ae
          filter_upwards [hν] with y hy
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hzero x hx])]
          have h := ((hasLaplacian_greenFunction_bounded_domain hV hVb hy).2 φ hφ).2.2
          simpa using h
    _ = (∫ x, φ x ∂(0 : Measure ℂ)) - ∫ x, φ x ∂ν := by rw [integral_zero_measure, zero_sub, integral_neg]


end HarmonicBalls
