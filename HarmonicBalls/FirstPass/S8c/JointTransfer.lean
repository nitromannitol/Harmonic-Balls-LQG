import Mathlib.MeasureTheory.Measure.Prod

/-! # Joint transfer of an almost-sure membership along a local domination

Pure measure theory, used in the local reduction of Lemma 8.2. If the root-side image of the restricted
root law is absolutely continuous with respect to the reference-side image of the product law, and the
reference-side observation lies almost surely in a measurable set `G`, then the root-side observation lies
almost surely in `G`. No probabilistic input is used beyond these hypotheses.
-/

open MeasureTheory

namespace HarmonicBalls

/-- Transfer of an almost-sure membership along an absolutely continuous image comparison. -/
theorem ae_mem_of_map_absolutelyContinuous {Ω Z E : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [MeasurableSpace E]
    (m : Measure (Ω × Z)) (ρ : Measure Z) (P : Measure Ω)
    (O : Ω × Z → E) (V : Z × Ω → E)
    (hO : AEMeasurable O m) (hV : AEMeasurable V (ρ.prod P))
    (hLD : m.map O ≪ (ρ.prod P).map V)
    {G : Set E} (hG : MeasurableSet G)
    (hGood : ∀ᵐ x ∂(ρ.prod P), V x ∈ G) :
    ∀ᵐ x ∂m, O x ∈ G := by
  have hGc : MeasurableSet Gᶜ := hG.compl
  have hV0 : (ρ.prod P).map V Gᶜ = 0 := by
    rw [Measure.map_apply_of_aemeasurable hV hGc]
    exact ae_iff.mp hGood
  have hO0 : m.map O Gᶜ = 0 := hLD hV0
  rw [Measure.map_apply_of_aemeasurable hO hGc] at hO0
  exact ae_iff.mpr hO0


end HarmonicBalls
