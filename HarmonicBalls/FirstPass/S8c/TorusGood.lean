import HarmonicBalls.FirstPass.S8c.TorusTail
import HarmonicBalls.FirstPass.S8c.GoodSet
import HarmonicBalls.FirstPass.S8c.UnitGood

/-! # Measurability of the torus-indexed good levels (input (iv) of LocalPhaseTailStep)

For a measurable family `ν : Ω → Measure ℂ`, the level-`n` good event on the phase torus times the field space is the
very-good criterion at scale `dyadicScale n` with torus phase `torusPhase p.1`, together with the annulus-ball
comparison, for the finite part of `ν p.2` (as in `GoodSet.lean`, where the finite part is the identity almost surely).
Its measurability follows from `measurableSet_phaseVeryGoodAnnulus` (Proofs/Sec8/PhaseVeryGoodScaling.lean), with the
unit good-annulus measurability of `UnitGood.lean` for threshold `a > 0`. These are the sets `Gn n` of
`ae_frequency_of_torus_dilation` (TorusTail.lean).
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- The level-`n` good event on the phase torus times the field space. -/
def torusGoodLevel {Ω : Type*} (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (n : ℕ)
    (ν : Ω → Measure ℂ) : Set (PhaseTorus × Ω) :=
  {p | PhaseVeryGoodAnnulus (finitePart (ν p.2)) β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃
      (torusPhase p.1) ∧
    AnnulusBallComparison (finitePart (ν p.2)) n 0 m}

/-- The level-`n` torus good events are measurable for a measurable family of measures and a positive threshold. -/
theorem measurableSet_torusGoodLevel {Ω : Type*} [MeasurableSpace Ω] (β : ℝ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (ha : 0 < a) (ν : Ω → Measure ℂ) (hν : Measurable ν) (n : ℕ) :
    MeasurableSet (torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m n ν) := by
  unfold torusGoodLevel
  have hμ : Measurable (fun p : PhaseTorus × Ω => finitePart (ν p.2)) :=
    measurable_finitePart.comp (hν.comp measurable_snd)
  have h1 : MeasurableSet {p : PhaseTorus × Ω |
      PhaseVeryGoodAnnulus (finitePart (ν p.2)) β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃
        (torusPhase p.1)} :=
    measurableSet_phaseVeryGoodAnnulus (A := PhaseTorus × Ω) hμ
      (fun p => isLocallyFiniteMeasure_finitePart (ν p.2))
      (c := fun _ => (0 : ℂ)) measurable_const (phase := fun p => torusPhase p.1)
      (measurable_torusPhase.comp measurable_fst) β (dyadicScale n) (dyadicScale_pos n) N₀ a b
      C₁m C₁p C₂m C₂p C₃ (measurableSet_unitGoodAnnulus a b ha)
  have h2 : MeasurableSet {p : PhaseTorus × Ω |
      AnnulusBallComparison (finitePart (ν p.2)) n 0 m} := by
    unfold AnnulusBallComparison
    exact measurableSet_le
      (measurable_const.mul ((Measure.measurable_coe measurableSet_ball).comp hμ))
      ((Measure.measurable_coe (measurableSet_annulus_local _ _ _)).comp hμ)
  rw [Set.ofPred_and]
  exact h1.inter h2


end HarmonicBalls
