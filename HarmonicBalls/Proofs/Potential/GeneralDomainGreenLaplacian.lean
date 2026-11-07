import HarmonicBalls.Proofs.Sec5.GeneralDomainInteriorGreen
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility
import HarmonicBalls.Steps.Sec2.GreenFunctionBall

/-! # Fixed-pole Green Laplacian on bounded domains

The potential-theoretic infrastructure uses work of Leonardo Bonanno. -/

namespace HarmonicBalls

open MeasureTheory Metric Filter Topology Set Laplacian InnerProductSpace

/-- The Green function with a fixed pole has distributional Laplacian minus
the unit mass at the pole on a bounded open domain. -/
theorem hasLaplacian_greenFunction_bounded_domain {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) {z : ℂ} (hz : z ∈ V) :
    HasLaplacian (greenFunction V z) 0 (Measure.dirac z) V := by
  obtain ⟨R, hR, hsub⟩ := hVb.subset_ball_lt 0 (0 : ℂ)
  obtain ⟨h, hh, heq⟩ :=
    exists_harmonicOnNhd_greenFunction_difference hV hVb hsub hz
  have hd0 := (greenFunctionBall R hR z (hsub hz)).1
  have hd : HasLaplacian (greenFunction (ball 0 R) z) 0 (Measure.dirac z) V :=
    ⟨hd0.1.mono_set hsub, fun φ hφ => hd0.2 φ ⟨hφ.1, hφ.2.1, hφ.2.2.trans hsub⟩⟩
  have hhL := hasLaplacian_zero_of_harmonicOnNhd hV hh
  have hl : LocallyIntegrableOn (fun x => greenFunction (ball 0 R) z x + h x) V :=
    hd.1.add hhL.1
  have hae : ∀ᵐ x ∂volume.restrict V,
      greenFunction (ball 0 R) z x + h x = greenFunction V z x := by
    rw [ae_restrict_iff' hV.measurableSet]
    filter_upwards [ae_ne_complex z] with x hxz hx
    have hx := heq x hx hxz
    linarith
  refine ⟨hl.congr hae, fun φ hφ => ?_⟩
  obtain ⟨h0, hzφ, hdφ⟩ := hd.2 φ hφ
  have hhφ := (hhL.2 φ hφ).2.2
  rw [integral_zero_measure, sub_zero] at hhφ
  have hi : ∫ x, greenFunction V z x * Δ φ x =
      ∫ x, (greenFunction (ball 0 R) z x + h x) * Δ φ x := by
    apply integral_congr_ae
    filter_upwards [ae_ne_complex z] with x hxz
    by_cases hx : x ∈ V
    · have h := heq x hx hxz
      congr 1
      linarith
    · rw [laplacian_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h)), mul_zero, mul_zero]
  refine ⟨h0, hzφ, ?_⟩
  rw [hi]
  have he : (fun x => (greenFunction (ball 0 R) z x + h x) * Δ φ x) =
      fun x => greenFunction (ball 0 R) z x * Δ φ x + h x * Δ φ x := by
    funext x; ring
  rw [he, integral_add (integrable_mul_laplacian_of_test hd.1 hφ)
    (integrable_mul_laplacian_of_test hhL.1 hφ), hhφ, add_zero]
  exact hdφ

#print axioms hasLaplacian_greenFunction_bounded_domain

end HarmonicBalls
