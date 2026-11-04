import HarmonicBalls.Proofs.Sec6.ExitTimeSpatialMap
import HarmonicBalls.Defs.Annuli

/-! # Transport of good annuli

A spacetime path-law identity and the corresponding geometric identities
transport the good-annulus predicate under a spatial homeomorphism.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set MarkovProcess
open scoped ENNReal

/-- A spatial homeomorphism transports good annuli when its spacetime path
homeomorphism transports the Brownian laws and maps the annulus and circle. -/
theorem isGoodAnnulus_map_of_spacetime_law
    (f : ℂ ≃ₜ ℂ) (c : NNReal) (hc : 0 < c)
    (hpath : ∀ x, (planarBrownianMotion x).map (spacetimePathHomeomorph f c hc) =
      planarBrownianMotion (f x))
    (μ : Measure ℂ) (r s : ℝ) (z w : ℂ) (a b : ℝ)
    (hA : f '' annulus z (3 * r) (5 * r) = annulus w (3 * s) (5 * s))
    (hS : f '' sphere z (4 * r) = sphere w (4 * s))
    (hg : IsGoodAnnulus μ r z a b) : IsGoodAnnulus (μ.map f) s w a b := by
  intro Y hY hYA hmass u hu
  let X := f ⁻¹' Y
  have hX : MeasurableSet X := f.measurable hY
  have hXA : X ⊆ annulus z (3 * r) (5 * r) := by
    intro x hx
    have : f x ∈ f '' annulus z (3 * r) (5 * r) := hA.symm ▸ hYA hx
    obtain ⟨y, hy, heq⟩ := this
    exact f.injective heq ▸ hy
  have hXY : f '' X = Y := image_preimage_eq Y f.surjective
  have hmass' : μ X ≤ ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) := by
    rw [Measure.map_apply f.measurable hY] at hmass
    rw [← hA, f.measurableEmbedding.map_apply, preimage_image_eq _ f.injective] at hmass
    exact hmass
  obtain ⟨v, hv, huv⟩ := hS.symm ▸ hu
  have hprob := hg X hX hXA hmass' v hv
  have heq := measure_exitTime_order_eq_of_spacetime_homeomorph f
    (annulus z (3 * r) (5 * r)) X c hc (planarBrownianMotion v)
    (planarBrownianMotion (f v)) (hpath v)
  rw [hA, hXY, huv] at heq
  rw [heq]
  exact hprob

end HarmonicBalls.Section6
