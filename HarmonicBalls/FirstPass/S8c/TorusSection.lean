import HarmonicBalls.FirstPass.S8c.TorusGood
import HarmonicBalls.FirstPass.S8c.PhaseTailProb

/-! # Phase sections of the level-0 torus good event (FIRST-PASS fp-S8c-8-2-local)

The probability bound (9) of `localPhaseTail_failure_le` is stated for the unit scale `ρ = 1` and a constant
phase, for the (locally finite) measure itself. The level-0 torus good event `torusGoodLevel _ 0 ν` uses
`dyadicScale 0` and the finite part of `ν`. These agree (`dyadicScale 0 = 1`, and the finite part is the identity
almost surely for a locally finite measure), so every phase section of the level-0 good event has failure probability
at most the bound of (9). This is the hypothesis `hsec` of `ae_frequency_of_torus_dilation`.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

/-- The dyadic scale at index zero is one. -/
theorem dyadicScale_zero_eq_one : dyadicScale 0 = 1 := by
  unfold dyadicScale
  norm_num

/-- A phase section of the level-0 torus good event has failure probability at most `ε`, when the unit-scale
failure bound holds for every constant phase and the measures are almost surely locally finite. -/
theorem torusGoodLevel_section_failure_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ν : Ω → Measure ℂ) (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω))
    (β : ℝ) (N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (ε' : ℝ≥0∞)
    (hbound : ∀ q : ℂ, P {ω | ¬ (PhaseVeryGoodAnnulus (ν ω) β 1 0 N a b C₁m C₁p C₂m C₂p C₃ q ∧
      AnnulusBallComparison (ν ω) 0 0 m)} ≤ ε')
    (θ : PhaseTorus) :
    P (Prod.mk θ ⁻¹' torusGoodLevel β N a b C₁m C₁p C₂m C₂p C₃ m 0 ν)ᶜ ≤ ε' := by
  refine le_trans (measure_mono_ae ?_) (hbound (torusPhase θ))
  filter_upwards [hloc] with ω hω hmem
  have hfp : finitePart (ν ω) = ν ω := finitePart_eq_of_locallyFinite (ν ω)
  simp only [torusGoodLevel, Set.mem_compl_iff, Set.mem_preimage, Set.mem_ofPred_eq] at hmem
  simp only [dyadicScale_zero_eq_one, hfp, not_and] at hmem ⊢
  exact hmem

#print axioms torusGoodLevel_section_failure_le

end HarmonicBalls
