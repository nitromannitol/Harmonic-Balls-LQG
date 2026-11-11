import HarmonicBalls.FirstPass.S8c.TorusGood
import HarmonicBalls.FirstPass.S8c.Measurability
import HarmonicBalls.FirstPass.S8c.GoodSet
import HarmonicBalls.Proofs.Sec8.PhaseVeryGoodScaling
import HarmonicBalls.Proofs.Sec8.AnnulusComparisonStationarity
import HarmonicBalls.Proofs.GFF.CommonContinuousCircleLQGVersion

/-! # helper: the per-phase failure bound on the profile space

Let `Q = P.map F` be the law of the measurable circle-average profile `F` of a field, and `Dec` the measurable map of
the frozen input E1 (`LQGMeasureOfProfileMeasurableFrozen`), so that `ν = Dec ∘ F` almost surely. The Ω-level bound
`P{¬(PVG (ν ω) q ∧ ABC (ν ω))} ≤ ζ/2` (from `s8d_phase_failure_all_q`) transfers to the profile law:
`Q{¬(PVG (Dec y) q ∧ ABC (Dec y))} ≤ ζ/2`. The argument: the bad profile set is `Q`-a.e. equal to its `finitePart`
version, which is Borel measurable (`measurableSet_phaseVeryGoodAnnulus`, `measurableSet_annulusBallComparison`); the
pushforward identity `Q S' = P (F⁻¹' S')` applies; and `P`-a.e. the preimage equals the Ω-level bad event of `ν`. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- The profile-level per-phase failure bound, transferred from the Ω-level bound along the circle profile. -/
theorem s8d_profile_hbound {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → C(CircleParameter, ℝ)) (hF : Measurable F)
    (Dec : C(CircleParameter, ℝ) → Measure ℂ) (hDec : Measurable Dec)
    (ν : Ω → Measure ℂ) (hDecν : ∀ᵐ ω ∂P, ν ω = Dec (F ω))
    (hloc : ∀ᵐ y ∂(P.map F), IsLocallyFiniteMeasure (Dec y))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (ha : 0 < a) (q : ℂ)
    (hΩ : P {ω | ¬ (PhaseVeryGoodAnnulus (ν ω) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ q ∧
      AnnulusBallComparison (ν ω) 0 0 m)} ≤ ENNReal.ofReal (ζ / 2)) :
    P.map F {y | ¬ (PhaseVeryGoodAnnulus (Dec y) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ q ∧
      AnnulusBallComparison (Dec y) 0 0 m)} ≤ ENNReal.ofReal (ζ / 2) := by
  have hμ : Measurable (fun y : C(CircleParameter, ℝ) => finitePart (Dec y)) :=
    measurable_finitePart.comp hDec
  have hM1 : MeasurableSet {y : C(CircleParameter, ℝ) |
      PhaseVeryGoodAnnulus (finitePart (Dec y)) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ q} :=
    measurableSet_phaseVeryGoodAnnulus (A := C(CircleParameter, ℝ)) hμ
      (fun y => isLocallyFiniteMeasure_finitePart (Dec y))
      (c := fun _ => (0 : ℂ)) measurable_const (phase := fun _ => q) measurable_const
      β 1 zero_lt_one N₀ a b C₁m C₁p C₂m C₂p C₃ (measurableSet_unitGoodAnnulus a b ha)
  have hM2 : MeasurableSet {y : C(CircleParameter, ℝ) |
      AnnulusBallComparison (finitePart (Dec y)) 0 0 m} :=
    (measurableSet_annulusBallComparison 0 0 m).preimage hμ
  set S' : Set (C(CircleParameter, ℝ)) := {y | ¬ (PhaseVeryGoodAnnulus (finitePart (Dec y)) β 1 0 N₀ a b
      C₁m C₁p C₂m C₂p C₃ q ∧ AnnulusBallComparison (finitePart (Dec y)) 0 0 m)} with hS'
  have hS'm : MeasurableSet S' := (hM1.inter hM2).compl
  -- the bad set and its finite-part version agree on the locally finite profiles
  have hSS' : {y | ¬ (PhaseVeryGoodAnnulus (Dec y) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ q ∧
      AnnulusBallComparison (Dec y) 0 0 m)} =ᵐ[P.map F] S' := by
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hloc] with y hy
    have key : (PhaseVeryGoodAnnulus (Dec y) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ q ∧
        AnnulusBallComparison (Dec y) 0 0 m) ↔
        (PhaseVeryGoodAnnulus (finitePart (Dec y)) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ q ∧
          AnnulusBallComparison (finitePart (Dec y)) 0 0 m) := by
      rw [finitePart_eq_of_locallyFinite (Dec y)]
    exact not_congr key
  -- the pushforward identity and the P-a.e. identification with the Omega-level bad event
  have hpre : (P.map F) S' = P (F ⁻¹' S') := Measure.map_apply hF hS'm
  have hEq : P (F ⁻¹' S') = P {ω | ¬ (PhaseVeryGoodAnnulus (ν ω) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ q ∧
      AnnulusBallComparison (ν ω) 0 0 m)} := by
    apply measure_congr
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hDecν, ae_of_ae_map hF.aemeasurable hloc] with ω hω hωl
    rw [hω]
    have key : (PhaseVeryGoodAnnulus (Dec (F ω)) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ q ∧
        AnnulusBallComparison (Dec (F ω)) 0 0 m) ↔
        (PhaseVeryGoodAnnulus (finitePart (Dec (F ω))) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ q ∧
          AnnulusBallComparison (finitePart (Dec (F ω))) 0 0 m) := by
      rw [finitePart_eq_of_locallyFinite (Dec (F ω))]
    exact not_congr key.symm
  calc P.map F {y | ¬ (PhaseVeryGoodAnnulus (Dec y) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ q ∧
        AnnulusBallComparison (Dec y) 0 0 m)}
      = (P.map F) S' := measure_congr hSS'
    _ = P (F ⁻¹' S') := hpre
    _ = P {ω | ¬ (PhaseVeryGoodAnnulus (ν ω) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ q ∧
        AnnulusBallComparison (ν ω) 0 0 m)} := hEq
    _ ≤ ENNReal.ofReal (ζ / 2) := hΩ

end HarmonicBalls
