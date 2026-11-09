import HarmonicBalls.FirstPass.S8c.TorusTail
import HarmonicBalls.FirstPass.S8c.TorusGood
import HarmonicBalls.FirstPass.S8c.TorusSection

/-! # The torus-indexed phase tail, reduced to the dilation (FIRST-PASS fp-S8c-8-2-local, LocalPhaseTailStep, torus form)

For a measurable family `ν : Ω → Measure ℂ` of locally finite measures, the level-`n` torus good events
`torusGoodLevel _ n ν` have the following almost-sure eventual frequency on the phase torus times the field law:
given the per-phase failure bound (9) at level `ζ/2`, a measure-preserving dilation `R` of the field space whose
doubling-dilation map `T = (phaseTorusDouble, R)` is ergodic, and the dilation identity `Gn n = T^[n]⁻¹' G` (G-8-2
section 3, eq. (10)), eventually `(1-ζ) N` good levels occur in each block `[N+1, 2N]`.

Everything is proved in this file or in the imported modules, except the three named inputs: the frozen Birkhoff
theorem (`BirkhoffPointwiseErgodic`), and the hypotheses `hergT` and `hid`, which are exactly the open
steps (ii) and (iii) of LocalPhaseTailStep (dilation identity on the field law; mixing of the GFF dilation).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- The torus-indexed phase tail from the Birkhoff theorem, given the dilation, its ergodicity, and the dilation
identity. -/
theorem torusPhaseTail_of_dilation (hB : BirkhoffPointwiseErgodic.{u}) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure ℂ) (hν : Measurable ν)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (ha : 0 < a) (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (hbound : ∀ q : ℂ, P {ω | ¬ (PhaseVeryGoodAnnulus (ν ω) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ q ∧
      AnnulusBallComparison (ν ω) 0 0 m)} ≤ ENNReal.ofReal (ζ / 2))
    (R : Ω → Ω) (hR : MeasurePreserving R P P)
    (hergT : Ergodic (fun p : PhaseTorus × Ω => (phaseTorusDouble p.1, R p.2))
      (phaseTorusFieldMeasure P))
    (hid : ∀ n : ℕ, torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m n ν =
      (fun p : PhaseTorus × Ω => (phaseTorusDouble p.1, R p.2))^[n] ⁻¹'
        torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m 0 ν) :
    ∀ᵐ p ∂(phaseTorusFieldMeasure P), ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤
        ∑ n ∈ Finset.Icc (N + 1) (2 * N),
          (torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m n ν).indicator (1 : PhaseTorus × Ω → ℝ) p :=
  ae_frequency_of_torus_dilation hB P R hR hergT
    (torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m 0 ν)
    (measurableSet_torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m ha ν hν 0) ζ hζ0 hζ1
    (fun θ => torusGoodLevel_section_failure_le P ν hloc β N₀ a b C₁m C₁p C₂m C₂p C₃ m
      (ENNReal.ofReal (ζ / 2)) hbound θ)
    (fun n => torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m n ν) hid

#print axioms torusPhaseTail_of_dilation

end HarmonicBalls
