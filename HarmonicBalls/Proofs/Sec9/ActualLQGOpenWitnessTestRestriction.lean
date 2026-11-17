import HarmonicBalls.Proofs.Potential.WholePlaneSourceFreeHarmonicity
import HarmonicBalls.Audit.GreenSubharmonicTestClass

/-! # Source-free restrictions of whole-plane tests

A whole-plane signed Green test with sources away from a bounded observation
set admits a bounded-witness representative with the same local values.
-/

namespace HarmonicBalls

open MeasureTheory Set InnerProductSpace

/-- If both compactly concentrated sources vanish on a neighbourhood of the
cluster closure, a whole-plane test has a bounded harmonic representative. -/
theorem bounded_representative_of_wholePlane_source_free
    {μ ν₁ ν₂ : Measure ℂ} {Λ U K₁ K₂ : Set ℂ} {z : ℂ} {q f : ℂ → ℝ}
    (hΛ : IsOpen Λ) (hΛb : Bornology.IsBounded Λ) (hz : z ∈ Λ)
    (hU : IsOpen U) (hΛU : closure Λ ⊆ U)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hf₁ : IsFiniteMeasure ν₁) (hf₂ : IsFiniteMeasure ν₂)
    (hν₁ : ν₁ K₁ᶜ = 0) (hν₂ : ν₂ K₂ᶜ = 0)
    (hν₁U : ν₁ U = 0) (hν₂U : ν₂ U = 0)
    (hq : HarmonicOnNhd q U)
    (hrep : ∀ x ∈ U, f x = (q + greenPotential univ ν₁ - greenPotential univ ν₂) x) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
      f z = g z ∧ f =ᵐ[μ.restrict Λ] g := by
  let : IsFiniteMeasure ν₁ := hf₁
  let : IsFiniteMeasure ν₂ := hf₂
  let g := q + greenPotential univ ν₁ - greenPotential univ ν₂
  have hg : HarmonicOnNhd g U :=
    (hq.add (harmonicOnNhd_greenPotential_univ_of_source_free_open hK₁ hν₁ hU hν₁U)).sub
      (harmonicOnNhd_greenPotential_univ_of_source_free_open hK₂ hν₂ hU hν₂U)
  refine ⟨g, harmonic_mem_boundedSubharmonicBallTestClass hΛb hU hΛU hg, ?_, ?_⟩
  · exact hrep z (hΛU (subset_closure hz))
  · filter_upwards [ae_restrict_mem hΛ.measurableSet] with x hx
    exact hrep x (hΛU (subset_closure hx))

end HarmonicBalls
