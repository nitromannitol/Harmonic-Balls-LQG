import HarmonicBalls.Proofs.Sec5.CompactGeneralDomainCompatibility
import HarmonicBalls.Proofs.Sec5.PuncturePotentialShift

/-! # An obstacle on a Green-regular domain

The enclosing-disc potential gives a continuous Laplacian shift on a bounded
open subdomain. The Green difference supplies continuity of the shifted
obstacle away from the pole. This uses the potential-theoretic infrastructure
of Leonardo Bonanno and the existing general-domain Green comparison.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- An enclosing-disc Green potential is a continuous distributional shift on
any open subdomain. It need not vanish on the subdomain boundary. -/
theorem enclosingDisc_potential_shift_on_domain
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hsub : U ⊆ ball (0 : ℂ) R) :
    ContinuousOn (greenPotentialBall μ R) (closure U) ∧
      HasLaplacian (greenPotentialBall μ R) 0 μ U := by
  refine ⟨(greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV).mono ?_,
    (greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR hV).mono_domain hsub⟩
  exact (closure_mono hsub).trans (closure_ball_subset_closedBall)

/-- The shifted obstacle is continuous up to a Green-regular boundary away
from the pole. The shift is the potential of an enclosing disc. -/
theorem continuousOn_greenRegular_shifted_obstacle
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) (t : ℝ)
    (hboundary : ∀ y ∈ closure U, y ∉ U →
      Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0)) :
    ContinuousOn (fun x => -t * greenFunction U z x + greenPotentialBall μ R x)
      (closure U \ {z}) := by
  obtain ⟨h, hc, _, heq⟩ :=
    exists_continuousOn_green_difference_of_boundary_limits hU hsub hz hboundary
  have hg : ContinuousOn (greenFunction U z) (closure U \ {z}) := by
    apply ContinuousOn.congr
      (((continuousOn_greenFunction_ball (hsub hz)).mono (by intro x hx; exact hx.2)).add
        (hc.mono sdiff_subset))
    intro x hx
    have hxz : x ≠ z := hx.2
    have h := heq x hx.1 hxz
    dsimp only [Pi.add_apply]
    linarith
  exact (continuousOn_const.mul hg).add
    ((enclosingDisc_potential_shift_on_domain hμ hR hV hsub).1.mono sdiff_subset)

#print axioms enclosingDisc_potential_shift_on_domain
#print axioms continuousOn_greenRegular_shifted_obstacle

end HarmonicBalls
