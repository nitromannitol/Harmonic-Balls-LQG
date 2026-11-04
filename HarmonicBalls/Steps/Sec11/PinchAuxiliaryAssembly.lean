import HarmonicBalls.Steps.Sec11.PinchConstrainedPaths
import HarmonicBalls.Steps.Sec11.PinchInternalDiam

/-! # Auxiliary-event assembly for a local pinch point

The additional constrained-path, radial-crossing and geometry hypotheses are
spelled out: their positivity and validity are not consequences of the printed
global-event lemma alone.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- At the origin and unit scale, the auxiliary events imply the strengthened
pinch event under explicit constrained-path and geometric hypotheses. -/
theorem pinchPointEventWithInternalBounds_of_auxiliary_events
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) (μ : MeasureTheory.Measure ℂ)
    (U V W T Q' Q : Set ℂ) (δ M : ℝ)
    (hfirst : pinchFirstEvent D W T Q' Q δ)
    (hsecond : pinchSecondEvent μ D U V δ M)
    (hthird : pinchThirdEvent D V W δ)
    (hpaths : (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric D ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 x) <
      ENNReal.ofReal (setDist D Q' (frontier Q)))
    (hclA : closure (T \ thickening (3 * δ) W) ⊆ ball 0 6)
    (hclB : closure (thickening (3 * δ) W \ V) ⊆ ball 0 6)
    (hclC : closure V ⊆ ball 0 6)
    (hsubA : thickening δ (T \ thickening (3 * δ) W) ⊆ ball 0 6)
    (hsubB : thickening δ (thickening (3 * δ) W \ V) ⊆ ball 0 6)
    (hsubC : thickening δ V ⊆ ball 0 6)
    (hAB : (closure (T \ thickening (3 * δ) W) ∩
      closure (thickening (3 * δ) W \ V)).Nonempty)
    (hBC : (closure (thickening (3 * δ) W \ V) ∩ closure V).Nonempty)
    (hcross : ENNReal.ofReal (setDist D {0} (sphere 0 δ)) +
        ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) +
        ENNReal.ofReal (setDist D (sphere 0 δ) (sphere 0 (2 * δ))) ≤
      ENNReal.ofReal (setDist D {0} (sphere 0 5))) :
    pinchPointEventWithInternalBounds μ D U T Q' Q M 1 0 := by
  have hres (A : Set ℂ) : rescaledSet A 1 0 = A := by simp [rescaledSet]
  have h1 := pinchFirstInternalBound_of_constrained_paths D Q' Q W δ hpaths
  have h2 := pinchSecondInternalBound_of_auxiliary_events hD hnonneg μ U V W T Q' Q δ M
    hfirst hsecond hthird hclA hclB hclC hsubA hsubB hsubC hAB hBC hcross
  simpa only [pinchPointEventWithInternalBounds, mul_one, hres] using ⟨h1, h2, hsecond.2⟩

end HarmonicBalls
