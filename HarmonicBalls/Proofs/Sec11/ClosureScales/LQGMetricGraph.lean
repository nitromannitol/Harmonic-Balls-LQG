import Mathlib

/-!
# Almost sure membership in a measurable graph

Source: the graph argument:
the joint law of the raw field and the coded circle averages is transported from the canonical model, and the canonical
joint law is concentrated on a Borel graph. The measure-theoretic core of this argument is that a pair of random
variables whose joint law is a measure `ν` with `ν Gᶜ = 0` for a measurable set `G` lies in `G` almost surely.
This file proves that core statement; the graph `G` and the joint law are supplied by the later steps.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter

/-- **Graph argument (measure-theoretic core).** If the joint law of `(F, K)` is a measure `ν` on `X × Y`, and `G` is a
measurable set with `ν Gᶜ = 0`, then `(F ω, K ω) ∈ G` for almost every `ω`. -/
theorem ae_mem_of_map_pair_eq {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    {P : Measure Ω} {F : Ω → X} {K : Ω → Y} (hF : Measurable F) (hK : Measurable K)
    {G : Set (X × Y)} (hG : MeasurableSet G) {ν : Measure (X × Y)}
    (hmap : P.map (fun ω => (F ω, K ω)) = ν) (hν : ν Gᶜ = 0) :
    ∀ᵐ ω ∂P, (F ω, K ω) ∈ G := by
  have hpair : Measurable fun ω => (F ω, K ω) := hF.prodMk hK
  rw [ae_iff]
  have h : {ω | ¬ (F ω, K ω) ∈ G} = (fun ω => (F ω, K ω)) ⁻¹' Gᶜ := rfl
  rw [h, ← Measure.map_apply hpair hG.compl, hmap, hν]

end HarmonicBalls
